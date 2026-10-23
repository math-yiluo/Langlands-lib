# Determinant-unit topology and conditional Levi decomposition

This internal assembly specializes the published normal-subgroup construction
to the actual determinant-unit subgroup of a product Levi. It proves the
required topological properties and converts the resulting decomposition into
the exact published Levi proposition, conditional on the four analytic inputs
and the Harish-Chandra equivalence. It does not prove those five inputs or the
unconditional host theorem.

The parameters are a prime `p`, an actual `F : PadicField p`, compatible
`T : F.TopologicalData`, and `B : BlockShape n`. The field universe `uF`
and representation-carrier universe `uV` are independent. Every topology is
obtained by installing `T.topology`. All natural ranks are allowed in this
conditional assembly; the eventual positive-rank theorem is a specialization.

## Actual subgroup topology

`determinantUnitNonarchimedean T B` proves `NonarchimedeanGroup` for
`determinantUnitSubgroup T B` with its subtype topology. The ambient Levi is
nonarchimedean by `T.leviNonarchimedean B`. A subgroup identity neighborhood
contains the inverse image of an ambient identity neighborhood, by the
induced-topology neighborhood formula. Choose an ambient open subgroup inside
that neighborhood and take its continuous inverse image along the actual
subgroup inclusion. Its containment proves the required neighborhood property.
The topological-group fields follow from the ambient group and subtype instances.
This is the elementary induced-topology argument also used in the published
`Langlands.Group.GL.CompactOpen` module.

`determinantUnitLocallyCompactSpace T B` proves local compactness for the
same subtype topology. The ambient Levi is locally compact by
`T.leviLocallyCompactSpace B`, and the published
`isOpen_determinantUnitSubgroup T B` makes the subgroup an open subspace.
Mathlib's `IsOpen.locallyCompactSpace` supplies the conclusion.

Neither result assumes the determinant-unit structure theorem, finite index,
central compactness, a Haar measure, or a representation-theoretic hypothesis.

## Conditional construction and exact-target reduction

`leviCompactProjector T B hsplit hstrata` constructs an actual ambient
equivariant endomorphism of every smooth complex Levi representation. It
specializes `CompactCoefficientClass.normalSubgroupProjector` to the actual
determinant-unit subgroup, using its published normality and the topology
proved above. Its inputs are precisely:

1. For every compact-coefficient class of the determinant-unit subgroup and
   every smooth representation `D` of that subgroup, the intrinsic isotypic
   subrepresentation and annihilator have complementary underlying submodules.
2. For each compact open subgroup, only finitely many compact-coefficient
   classes have a nonzero fixed vector.

Both class representatives and ambient representations use carrier universe
`uV`; no resizing assumption is introduced.

`leviQuasicuspidalDecomposition_of_inputs` additionally assumes:

3. The total intrinsic isotypic subrepresentation of every smooth subgroup
   object has compact smooth-dual coefficients.
4. Every smooth subgroup object with compact smooth-dual coefficients has
   total intrinsic isotypic subrepresentation equal to top.
5. The published proposition `LeviHarishChandraTheorem.{uF,uV}`.

Its conclusion is exactly
`LeviQuasicuspidalDecompositionTheorem.{uF,uV} F T B`. The proof first applies
`decomposition_of_normalSubgroup_compactCoefficients`, obtaining actual
ambient invariant subspaces `S,Q` with complementary underlying submodules.
The compactness of the restriction to `S` is converted to quasicuspidality
using the reverse direction of the supplied Harish-Chandra equivalence.
For every actual smooth subquotient `D` of `Q`, the forward direction
converts its quasicuspidality to compactness after restriction; the generic
decomposition then shows that `D` is a subsingleton.

The subgroup restriction in `SmoothRep.restrictSubgroup` and the specialized
`determinantUnitRestriction` retain the same carrier and compose the action
with the same subgroup inclusion. Their representations agree definitionally,
so the proof applies the Harish-Chandra equivalence directly. It retains
arbitrary smooth representations and the full actual-subquotient conclusion,
without admissibility, irreducibility, finite length or finite dimension.

The provenance is an internal specialization of the imported published
constructions, the induced-topology neighborhood formula and open-subspace
local compactness. No new literature theorem is asserted. In particular,
the Harish-Chandra proposition is an explicit premise, not an imported proof.
