# The actual scalar-extension Weil unit

For a finite projective commutative ring extension `S/R` and an affine
locally finite-type group scheme `G` over `Spec R`,
`Langlands.GroupScheme.AffineWeil.unit` constructs the actual group-scheme unit
`G → AffineWeil.groupScheme R S ((GroupScheme.baseChange (Spec.algebraMap R S)).obj G)`
using precisely the existing scheme base change and the existing affine
Weil restriction.

Its affine point formula, `unit_affinePoints`, is extension along
`a ↦ 1 ⊗ a`, followed by the existing actual multiplicative base-change
point comparison `affinePointsBaseChangeMulEquiv`. It holds for every
commutative `R`-algebra. The restriction's `pointsEquiv` is the fixed
comparison appearing in this identity, so the construction retains the
actual group laws and coefficient maps.

If `S` is also faithfully flat over `R`, `isClosedImmersion_unit` proves that
the underlying scheme map is a closed immersion. The field specialization
`isClosedImmersion_unit_of_field` supplies that conclusion for every finite
extension of fields in an arbitrary common universe. The module proves
this specialization without a faithful-flat premise in its type: the
field-module instances supply faithful flatness. In particular all finite
separable extensions, arbitrary number fields, nonsplit groups and
noncommutative groups are covered. No smoothness, connectedness or
reductivity hypothesis is used.

The construction uses the canonical global-section affine presentation of
the original group, the existing corepresented group homomorphism
construction and the actual tensor-valued Weil representing equivalence.
The source coordinate model is identified with the original group as a
group scheme, using the published `AffineCorepresentation` construction.
Naturality in every coefficient algebra is proved using the first
projection of the actual pullback, together with functoriality of tensor
extension. The induced corepresented group homomorphism, composed with the
inverse source presentation, gives the actual unit. The corepresentation's
affine-point formula and cancellation of the source presentation prove
`unit_affinePoints`.

For the closed-immersion proof, `unitCoordinateMap` names the classifying
map from the Weil coordinate algebra to the original global-section
algebra. The underlying unit map is definitionally its spectrum preceded
by the inverse affine presentation; `unit_hom_left` records this.

Scalar extension of the original presentation point is an isomorphism.
The proof identifies it with the inverse canonical tensor presentation of
a base-changed spectrum followed by the base change of the original
presentation. This identity is checked using the actual two pullback
projections. Consequently the upper-base coordinate algebra map is
surjective. The Weil representing property expresses that map as scalar
extension of `unitCoordinateMap` composed with the universal point.
Surjectivity of the composite proves surjectivity of the scalar-extended
classifying map. Mathlib's faithful-flat criterion for linear maps
descends it to surjectivity of `unitCoordinateMap`. Its spectrum is
therefore a closed immersion, and composition with the affine presentation
preserves that property.

The provenance is an internal derivation from the existing representing
bijections, actual pullback base-change comparisons, affine
corepresentations, and Mathlib's faithful-flat reflection of surjectivity
and affine closed-immersion criterion. Neither a supplied retraction nor
a supplied immersion is assumed. No rational-character kernel comparison,
adelic quotient embedding or compactness conclusion is asserted here.

The general coordinate-recovery identity is already available as
`Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLine.affineRingPointEquiv_ringTestMap'`
in [GaloisTwistedLineTopology](../AlgebraicGeometry/AlgebraicSpace/GaloisTwistedLineTopology.md).
This module does not duplicate that declaration; the unit construction
and its proofs do not require it.
