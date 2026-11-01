# CM transport of actual quotient intertwiners and classes

This internal construction extends the actual quotient CM transport in
`OperatorSubquotientCMTransport` to maps and whole-action isomorphism classes.
It follows the map-conjugation route already implemented for embedded
realizations in `OperatorCMTransportClasses`, applied here to actual module
quotients. An actual CM number field has arbitrary universe, the rank is
any natural number, and coefficients remain complex.

`OperatorSubquotient.Intertwiner` abbreviates the genuine complex linear
intertwiners between the two whole-operator quotient representations.
For such an intertwiner `L`, its constructed `complexConj` is
`C_T ∘ L ∘ C_Q⁻¹`, using the existing induced quotient linear equivalences.
Inverse covariance for `C_Q` reduces its intertwining identity to that of
`L` at the actual conjugated operator, followed by forward covariance for
`C_T`. The application formulas, identity and composition laws follow
from the two inverse identities. Twice conjugation is naturally identified
with the original map through the actual `complexConjTwiceEquiv` maps;
the proof applies the forward application formula twice.

`Equivalence.complexConj` uses the same map and the composition of the three
actual linear equivalences. It preserves the underlying intertwiner,
identity, composition and inverse, with exact application formulas.
Its finite restriction has that same application formula on the entire
quotient carrier. It chooses no local tensor factor and assumes no
factorization.

The actual CM construction preserves and reflects whole-action equivalence.
For reflection, apply it to the supplied equivalence and compose with the
canonical twice-CM whole-action equivalences at both ends. This route does
not identify dependent numerator and denominator presentations by equality.
It proves that `IsoClass.complexConj` is well defined on the existing
whole-operator quotient classes. Quotient induction and the canonical
twice-CM equivalence prove involutivity. Thus `IsoClass.complexConjEquiv`
is a self-equivalence with equality reflection, sending the class of each
actual quotient to the class of its actual CM image.

Provenance is internal: only actual induced quotient maps, proved covariance,
genuine representation equivalences and the existing class setoid are used.
No new identification with original literature is claimed. Complex values
are fixed; CM acts on the original function argument before taking the
module quotient. The maps here are algebraic, and arbitrary intertwiners
need not be continuous. No quotient evaluation, topology, separate CM
operation on all finite smooth classes, central-character or cusp condition
on arbitrary quotients, conjugate self-duality, or irreducible or spectral
existence is asserted.
