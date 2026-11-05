# Integral matrices from compact sets of actual rational points

This internal adapter bundles the actual `MatrixRepresentation.rationalMatrix`
as a continuous matrix-valued map for the canonical identity-test rational-point
topology. Each entry is evaluation of the pullback of its general-linear
coordinate section. The canonical affine scheme/algebra-point comparison
identifies that evaluation with the existing topology.

Over a nonarchimedean local field, the finite union of the images of a compact
point set under all matrix entries is compact. Its nonzero valuative upper bound
is a common bound on every entry on that point set. If all nonnegative powers
of a point lie in such a compact set, the actual representation respects powers,
and `BoundedMatrixPowers` makes the point's matrix integral over the canonical
valuation integer subring.

The whole-group specialization assumes compactness and is only an internal
conditional lemma. The anisotropic torus specialization obtains that compactness
from `IsAnisotropic.isCompact_univ_of_isTorus`, whose independent proof uses the
torus norm kernel. It therefore proves integrality of every actual torus
representation matrix and the exact
`MatrixRepresentation.HasIntegralCharacteristicPolynomials` predicate for
anisotropic tori. It does not assume or prove general reductive compactness.
All natural dimensions, including zero, and both local-field characteristics
are retained; no faithfulness hypothesis is used.
