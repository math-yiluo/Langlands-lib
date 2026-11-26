# A presented finite component in its cuspidal Hilbert summand

`PresentedLocalComponentHilbertOccurrenceStatement` fixes a number field
with compact adelic quotient and the central data for the
positive-central quotient of the general linear group. Suppose a
cuspidal operator realization has a linear map into the full cuspidal
Hilbert space sending its forms to their quotient classes, with range
in a submodule `P`. The irreducible finite component of a supplied
spectral presentation then has a nonzero local intertwiner into `P`
after identifying the matrix and group-scheme local actions.

The class map is injective because each quotient class has a continuous
representative and the quotient Haar measure is positive on nonempty
open sets. Compose it with the actual inclusion of the presented
component in the cuspidal realization. The finite quotient class
equivariance and `adelicHomeomorph_ofPlace` give the required local
equivariance.

`presentedLocalComponentEquivOfHilbertOccurrence` also assumes that `P`
is complete, invariant and irreducible among closed invariant subspaces.
It takes a nonzero local intertwiner into `P` from another irreducible
admissible representation. The local isotypy theorem applied to this
intertwiner identifies that action with the presented finite component.
The identification uses the smoothness and irreducibility of the local
component after transport to the group-scheme local points.
