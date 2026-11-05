# Isometric representative transport on the actual product-induced source

This derived construction implements the Hermitian compatibility of
Waldspurger's canonical representative transport in VI.1, printed p.295 /
PDF p.61. It uses the actual product-induced coefficient source from V.1,
printed p.288 / PDF p.54, and its inverse-degree positive Hermitian form
from V.2, printed p.293 / PDF p.59. The registered source is
`waldspurger-2003-plancherel`. The actual Schur degree uses III.1(3),
printed p.265 / PDF p.31, through the published formal-degree comparison.
The compact normalization and smooth-dual pairing come from the existing
I.3 construction, printed p.243 / PDF p.9.

All source-form hypotheses remain explicit: the semidirect decomposition of
the parabolic, closed unipotent and parabolic subgroups, local compactness
of the parabolic, a supplied compact open subgroup with `G = P K`,
ambient unimodularity, the full parabolic modulus identity, second
countability and Borel measurability. The ambient group universe and the two
representation-carrier universes are independent. Compact open subgroups
of the Levi must be cofinal for the actual smooth-dual Hermitian forms.
These are conditional generic constructions; no rational-point realization
of the structural inputs is claimed.

`productForm_ofEquiv` proves that the entire source form commutes with the
published pointwise `productInducedCoefficientTransport` when the inducing
form is pulled back along the given equivalence. Both inducing
representations are admissible. The proof uses the compact induced
Hermitian pullback comparison in the vector factor and the proved
`dualInvariantForm_ofEquiv` in the dual factor. The published product
tensor equivalence is surjective. Double tensor induction therefore reduces
the whole-form comparison to the pointwise transport formula and the two
factor comparisons. No irreducibility assumption is used in this lemma.

`productForm_equiv` allows arbitrary positive forms on the two inducing
representatives when the source is irreducible admissible. It combines the
previous comparison with the published independence of the entire source
form from the positive inducing form. Schur's lemma acts on the inducing
representation.

For `formalDegreeProductForm_ofEquiv`, both inducing representations are
irreducible and square integrable modulo the same specified normal
central subgroup of the Levi. The quotient has its Borel structure and a
fixed inversion-invariant Haar measure. The proof obtains a positive form
from the published square-integrability unitarity theorem, computes both
canonical source forms using this form and its pullback, applies
`productForm_ofEquiv` and the published equality
`representationFormalDegree_equiv`, and concludes by form extensionality.
The quotient measure and compact probability are fixed on both sides.

`formalDegreeProductTransport` constructs the existing equivariant
pointwise source equivalence together with this full inverse-degree
Hermitian isometry property, as a subtype of the existing representation
equivalences. Its underlying map is
`productInducedCoefficientTransport`. The theorem
`formalDegreeProductTransport_independent` reuses the published Schur
choice-independence theorem to prove equality of these isometric
transports for any two inducing equivalences.

With Hausdorff ambient topology and continuous Levi projection,
`coefficientMap_transport` proves preservation of the actual compact
probability coefficient function by the same underlying transport.
Both sides are the integral of their original diagonal contraction
against the same compact Haar probability. Published pointwise
contraction naturality makes the integrands equal.

This construction does not assume irreducibility of parabolic induction.
It does not identify different choices of Haar normalization, establish
the structural hypotheses on arbitrary rational-point groups, or
construct the spectral family and orbit measures. Those remain separate
obligations in the Plancherel program.
