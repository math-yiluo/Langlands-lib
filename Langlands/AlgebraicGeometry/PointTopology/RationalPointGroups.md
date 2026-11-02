# Group operations on identity-test rational points

This derived host adapter equips the already published canonical rational-point
homeomorphism with its actual group compatibility. It does not introduce a group
law or a topology. Both point carriers carry Mathlib's existing Hom group of the
same group scheme.

## Source and scope

The source motivation is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Proposition 2.1 and the following paragraph, printed
pages 2–3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The group topology theorem is already proved on the actual `RingPoint` carrier
in `AffineGroupProofs`. The present unit derives its identity-test convention
from `RationalPoints`, so its comparisons are internal consequences rather than
additional claims attributed to the paper.

The base ring `R : Type u` is an arbitrary commutative ring and `G` is an actual
group scheme over `Spec R`. The group equivalence requires no affineness,
finiteness or topology. Its topological comparison requires `G.X.left` affine
and an arbitrary topology on `R`. The topological-group and inversion results
add `IsTopologicalRing R` and `LocallyOfFiniteType G.X.hom`. No field, locality,
open-unit, separation, Hausdorff, compactness or local-compactness assumption
is used. The universe remains arbitrary.

## Constructions and implemented comparisons

All declarations are in `Langlands.AlgebraicGeometry.PointTopology`.
`rationalPointGroupEquiv R G` upgrades `rationalPointEquiv R G.X` to a
multiplicative equivalence. Its forward function and inverse are the existing
identity-test comparison. Reducing the identity-test isomorphism and the existing Hom operations
proves multiplication compatibility by definitional equality. Thus the unit preserves both underlying scheme morphisms and
existing group operations.

`rationalPointGroupHomeomorph R G` combines this multiplicative equivalence
with `rationalPointHomeomorph R G.X`. Its domain is equipped explicitly with
`rationalPointTopology R G.X`; its codomain has the published affine evaluation
topology. No global topology instance is installed on identity-test points.

`rationalPoint_isTopologicalGroup R G` transfers the published
`affineGroupTopological_proof R R G` through the inducing group equivalence.
The conclusion uses exactly the existing Hom group operations on
`RationalPoint R G.X` with the named canonical topology. Finally,
`continuous_rationalPoint_inv R G` selects the continuous inversion operation
of that topological group. This inverse is the categorical Hom inverse, given
by postcomposition with the group-scheme inversion morphism.

`rationalPoint_t2Space R G` transfers Hausdorffness from the published
RingPoint result through the homeomorphism. It assumes only `T2Space R`
beyond the affine and topology hypotheses, without finiteness or continuous
ring operations. `rationalPoint_locallyCompactSpace R G` similarly transfers
local compactness using the published result for a Hausdorff locally compact
topological ring and a locally finite-type affine group scheme. Both use
exactly the named rational-point topology.

This comparison does not assert compactness of proper-scheme points,
surjectivity of an actual flag-orbit map, compactness of a parabolic quotient,
nonarchimedean subgroup bases or a scheme-GL/matrix topology comparison. Those
remain separate obligations.
