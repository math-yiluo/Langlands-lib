# Geometric smooth surjectivity from the actual differential

`SmoothSurjectiveOfSurjectiveDifferentialStatement` isolates an internal
geometric prerequisite for the smooth semigroup quotient comparison.
It is a proposition target; this module supplies no proof of it.

For any field `k` in an arbitrary universe, let `f : H ⟶ G` be an actual
homomorphism of smooth affine group schemes over `k`, and suppose `G` is
connected. The hypothesis is surjectivity of the actual linear differential
`targetMapLinear f k`, defined on the dual-number identity kernels. The
conclusion is smoothness and surjectivity of the actual underlying scheme
morphism `f.hom.hom.left`. Surjectivity here is Mathlib's scheme morphism
property. It does not assert surjectivity on points over every original
test algebra or test scheme. Connectedness of `H` is not assumed.

The mathematical route motivating this target is the differential criterion
for smoothness between smooth schemes at a rational point, followed by
translation in group schemes and descent from field extensions. A smooth
homomorphism has open image; the image subgroup in the connected target
then fills the target. These are proof obligations, not hypotheses hidden
in the definition. The statement imposes no split-torus action, semigroup
realization or semigroup comparison assumption, so it can be used
independently of the comparison theorem.
