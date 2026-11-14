# Upper building data from the supplied unramified apartment

Author: Worker 200.

The internal definition `MaximalUnramified.buildingDataOfApartment` packages
the upper apartment, maximal split torus, centralizer and integer-valuation
compatibility supplied by the fixed-point depth-zero statement into
`MaximalUnramified.BuildingData`.

The generic group is the base change of the original connected reductive
group from `F` to its inertia fixed field. Its connected reductivity follows
from the published `IsConnectedReductive.baseChange_of_algebraicExtension`.
All other fields are exactly the supplied data. No topology or apartment
axiom beyond those encoded in that datum is asserted.

This construction does not give the lower-field building or the integral
models required by the depth-zero proof.
