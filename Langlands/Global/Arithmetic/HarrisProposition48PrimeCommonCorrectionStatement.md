# One parity correction on the actual orbit presentations

Harris (1998), printed p. 195, normalizes the infinity type using a half-norm
power of specified parity. The general-coefficient remark and the prime-orbit
argument on pp. 202–203 require comparison of corrected presentations at the
same auxiliary place. For the orbit, one takes the correction of the identity
child, transports it to the cyclic step field, and applies that single
character to every raw orbit member.

`TransportedParityCorrectionStatement` supplies regular algebraicity and
conjugate self-duality of the actual realization obtained by this procedure.
Arithmetic pullback of the originally corrected realization carries its
enveloping action by the transport of the complexified Lie algebra, which
permutes the dominant integral weights by the embeddings. The quotient of
the new correction by the pulled-back old correction has integral infinity
type because their half-norm factors agree. Its determinant multiplication
shifts the highest weights as in Clozel (1990), Définitions 1.8 and 3.12.
Arithmetic pullback commutes with the CM involution. The conjugate-inverse
characters cancel on the two sides of the conjugate-contragredient pairing
and their Lie differentials sum to zero. The underlying linear equivalences
preserve the contragredient functionals.

`WeakInductionDeterminantTwistStatement` attaches the corrected inducing
character to the genuine twisted presentation. In Definition 1.3(b), printed
p. 186, the norm at each good place over `v` gives the residue-degree power
of the base uniformizer modulo units. This agrees, factor by factor in the
whole product over the places above `v`, with scaling the spectral variable
by the value of the base correction on the uniformizer.

`CuspidalPresentationDeterminantTwistSupercuspidalStatement` uses the actual
local component of the same twisted presentation. The determinant character
is trivial on the unipotent radical of each proper parabolic, so twisting
preserves the Jacquet vanishing criterion. The published local twist
equivalence also preserves irreducibility and admissibility. This supplies
the supercuspidality premise of the forward comparison for the corrected
component coming from the chosen raw one.

`Proposition48PrimeCommonCorrectionStatement` groups the three inputs.
The base number-field, extension field, and spectral-carrier universes are
independent.
