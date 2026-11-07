# Actual reduced-norm-one groups of central simple algebras

Let `k : Type u` be a field and let `A : Type u` be an associative unital
`k`-algebra with
`[FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]`.
This internal construction gives the actual reduced-norm character of its
algebra-unit group and its actual closed affine norm-one group scheme.
There is no supplied splitting field or chart and no restriction on
characteristic or perfectness.

The namespace is `GroupScheme.CentralSimpleUnits`.
The unit group `groupScheme k A` is the existing
`FiniteAlgebraUnits.groupScheme` with the canonical finite basis
`Module.finBasis k A`. Its actual point models and smoothness come from
that construction.

The published `CentralSimple.reducedNorm` supplies its own finite Galois
splitting field and actual chart. Using these constructed data in
`FiniteAlgebraUnits.GaloisNorm.norm` gives `reducedNormHom k A`.
The defining polynomial norm of that character is exactly the published
unconditional reduced norm.
The theorem `reducedNormHom_points` therefore identifies its value on every
relative test scheme with `CentralSimple.reducedNormUnits k A` on the
actual tensor algebra of relative global sections.
The theorem `reducedNormHom_affine_points` identifies its value on every
commutative affine coefficient algebra `R` with the same published
operation `reducedNormUnits k A R`.
The coefficient algebra may be nonreduced or trivial.

The group `normOne k A` is the actual group-scheme kernel of
`reducedNormHom k A`, and `normOneι k A` is its actual inclusion.
The closed-immersion, affineness and locally-finite-type results follow
from the corresponding proved properties of the charted construction
applied to the constructed splitting chart.
No kernel smoothness, connectedness, reductivity or simple-connectedness
assertion is made here.

The equivalence `normOnePointsEquiv k A T` identifies actual kernel points
on any test scheme `T` with the published subgroup
`CentralSimple.reducedNormOne k A (((algΓ k).obj T).unop)`.
The source of the coefficient tensor algebra is the actual relative
global-section algebra. The equivalence is natural for every actual
test pullback through `normOneUnitsRestrict`.

The equivalence `normOneAffinePointsEquiv k A R` gives the same
identification on each affine coefficient algebra.
The equivalence `normOneRationalPointsEquiv k A` identifies actual rational
points with `CentralSimple.reducedNormOne k A k`, the published subgroup
of `(k ⊗[k] A)ˣ`. The value formulas for all three comparisons respect the
actual inclusion into the algebra-unit group.

The theorem `reducedNormHom_eq_from_chart` additionally proves equality of
actual group-scheme morphisms when the character is constructed using any
finite Galois splitting field `L : Type u` and any actual chart of size
`Fin (CentralSimple.reducedDegree k A)`. Both constructions use the
canonical finite coordinate basis of the same actual unit group.
The proof compares their actual points through the `Gm` equivalence and
applies the published all-test splitting independence of the reduced norm.

The provenance is internal specialization of the proved charted
group-scheme construction to the published constructed finite Galois
chart, followed by its proved unconditional norm comparison.
The norm-one point targets are the existing reduced-norm kernels;
no norm operation or structural law is supplied as an extra premise.
Elementary-root geometry, arithmetic generation or SK1, general
factor-model classification, and the unrestricted local Kneser–Tits
theorem remain separate obligations.
