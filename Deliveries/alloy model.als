module myTaxiService

//SIGNATURES//

sig Text{}
enum driverStatus {available, busy, offline}
enum requestStatus {active, pending, inactive}

abstract sig User{
	email: one Text,
	username: one Text,
	password: one Text,
	name: one Text,
	surname: one Text,
	telephone: one Text,
	location: lone Coordinates}

sig Passenger extends User{}

sig Driver extends User{
	licenseNumber: one Int,
	ID: one Int,
	numberPlate: one Text,
	driverLicense: one Text,
	status: one driverStatus}

abstract sig Request{
	pickUpPoint: one Coordinates,
	numberOfPassengers: one Int,
	sender: one Passenger,
	receiver: lone Driver,
	isActive: one requestStatus}

	{numberOfPassengers>=1}

sig Call extends Request{}

sig Reservation extends Request{
	destination: one Text,
	time: one Text}

sig Coordinates{
	latitude: one Text,
	longitude: one Text,
	belongsTo: one Zone}

sig Zone {
	queue: set Driver,
	border: set Coordinates,
	reservations: set Reservation}

one sig City {
	name: one Text,
	zones: set Zone}


//FACTS//

fact userProperties{
//every email is unique
	no disj u1, u2 : User | u1.email = u2.email
//every username is unique
	no disj u1, u2 : User | u1.email = u2.email
//every telephone number is unique
	no disj u1, u2 : User | u1.telephone = u2.telephone
	}

fact driverProperties{
//every license number is unique
	no disj d1, d2 : Driver | d1.licenseNumber = d2.licenseNumber
//every ID is unique
	no disj d1, d2 : Driver | d1.ID = d2.ID
//every plate number is unique
	no disj d1, d2 : Driver | d1.numberPlate = d2.numberPlate
//every driver license is unique
	no disj d1, d2 : Driver | d1.driverLicense = d2.driverLicense
//if a driver is a receiver of an active request, he is busy
	all d : Driver, r : Request | r.isActive = {active} and r.receiver = d implies d.status = {busy}
//if a driver is not offline, he surely has the location attribute
	all d : Driver | d.status!={offline} implies #d.location=1
	}

fact requestProperties{
//there can't be two active requests with the same sender
	no r1, r2 : Request | r1.isActive = {active} and r2.isActive = {active} and r1.sender = r2.sender
//there can't be two active requests with the same receiver
	no r1, r2 : Request | r1.isActive = {active} and r2.isActive = {active} and r1.receiver=r2.receiver
	}

fact zoneProperties{
//the zones are clearly divided
	all disj z1, z2 : Zone | z1 & z2 = none
//in the queue there are only available drivers
	all z : Zone, d : Driver | d in z.queue implies d.status = {available}
//in the reservations set there are only pending reservations
	all z : Zone, r : Reservation | r in z.reservations implies r.isActive = {pending}
	}


//FUNCTIONS//

fun activeRequests [] : set Request {
//returns the set of all active requests
	{r: Request | r.isActive = {active}}
	}


//ASSERTIONS//

assert availableDriversNoReceivers{
//a driver who is available is not a receiver of an active request
	no d : Driver | d.status = {available} and d in activeRequests.receiver
	}
check availableDriversNoReceivers for 3

assert offlineDriver{
//if a driver is offline, he is neither a receiver of an active request nor in the queue of a zone
	no d : Driver | d.status = {offline} and d in activeRequests.receiver+Zone.queue
	}
check offlineDriver for 3

assert coordinateInOneZone{
//a coordinate belongs only to one zone
	no disj z1, z2 : Zone, c : Coordinates | c.belongsTo in z1 and c.belongsTo in z2
	}
check coordinateInOneZone for 4


//PREDICATES//

pred showRequest {
	#Passenger>1 and #Driver>1 and #Request>1
	}

run showRequest for 4

pred show {}

run show for 3
