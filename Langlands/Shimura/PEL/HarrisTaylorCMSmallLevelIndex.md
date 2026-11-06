# Ordered sufficiently small levels for the actual CM tower

Author: Worker 57.

This internal construction supplies the inclusion index of the existing CM
scheme tower. It proves conditional cofilteredness and cofinality for
shrinking-level colimits and records conjugation stability in the convention
of the published generic colimit action.

## Actual level categories and functors

For an algebra involution `σ : AlgebraInvolution ℚ B`, with B a ring and a
ℚ-algebra in any universe, put `G = σ.FiniteAdelicPointsᵐᵒᵖ`. The existing
`σ.SmallLevelCategory` is the full subcategory of `CompactOpenLevel G`
cut out by `σ.LevelSufficientlySmall`. Its arrows retain their translating
elements. That smallness predicate is the local finite-order condition from
[SufficientlySmallLevels](../Unitary/SufficientlySmallLevels.md).

`σ.OrderedSmallLevel` is instead the subtype of `CompactOpenLevel.Ordered G`
satisfying the same predicate, with the induced preorder. Its arrows express
inclusions of the underlying subgroups. These two categories have the same
objects and different morphisms.

`σ.orderedSmallLevelForget` includes the ordered category into all ordered
compact open levels. `σ.orderedSmallLevelToSmallLevelCategory` maps it into
the genuine small transporter category: every inclusion goes to the actual
transporter with translating element one. Identity and composition follow
from the corresponding actual transporter equalities.

`orderedSmallLevelToSmallLevelCategory_comp` proves that forgetting the
smallness certificate before or after forming those transporter arrows gives
the same functor to `CompactOpenLevel G`. The equality is reflexivity.
`orderedSmallLevel_nonempty_iff` compares existence of objects in the two
small-level categories in both directions.

## Refinements and conditional cofinality

The following constructions additionally require `Module.Finite ℚ B`.
The imported finite-adelic topology then gives the topological group structure
needed for intersections and conjugation.

For a small ordered U and any compact open V,
`σ.orderedSmallLevelRefinement U V` has underlying compact open level
`CompactOpenLevel.inf U.val V`. Its smallness follows from U's certificate
by the published subgroup monotonicity theorem. The `_val` lemma identifies
the underlying intersection by reflexivity.

Intersections give `IsDirected σ.OrderedSmallLevel (· ≥ ·)`.
If `Nonempty σ.SmallLevelCategory` is supplied, these indices are nonempty
and cofiltered. `exists_orderedSmallLevel_le` then refines any V by
intersecting V with one existing small U. Its conclusion retains the actual
subgroup inclusion.

The instance `orderedSmallLevelForget_initial` proves that the forgetful
ordered inclusion is an initial functor under the same nonemptiness premise.
It uses Mathlib's cofiltered initiality criterion: the intersections give an
object over every target, and any two arrows in the target preorder are
equal. Its opposite is therefore final, so it can be used in the usual
cofinal change of index for colimits of diagrams defined on all ordered
levels. The construction does not extend a diagram defined only on small
levels to other levels.

## Conjugation convention

The published `CompactOpenLevel.conjugate U g` from
[HarrisTaylorCMConjugationSchemes](HarrisTaylorCMConjugationSchemes.md)
has subgroup g⁻¹ U g. The `CompactOpenLevel.conjLevel g U` used by
[LevelColimit](../LevelColimit.md) has subgroup g U g⁻¹.

`LevelSufficientlySmall.conjLevel` applies the published smallness theorem
for `conjugate` with g⁻¹. Its conclusion uses exactly the generic colimit
conjugate. `σ.orderedSmallLevelConjugate g U` packages that actual level with
its inherited smallness certificate; the `_val` formula is reflexivity.
No nonemptiness premise is needed for this construction at a specified U.

## CM specialization

Let `D : CentralSimpleUnitaryData E F A n` with universe-zero totally real
number field E, totally complex number field F, the displayed quadratic
extension and algebra structures and scalar towers. This index construction
does not require signature charts, geometric representability, polarizations
or coefficient objects.

`OrderedSmallCMLevel D` is
`D.rationalInvolution.OrderedSmallLevel`. The entry definition
`orderedSmallCMLevelToSmallCMLevel` is the preceding transporter inclusion
for this precise involution. It therefore indexes the domain of the existing
CM scheme tower, retaining its exact smallness predicate and inclusion maps.
`orderedSmallCMLevelForget` includes it into all ordered compact open levels
of `D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`. The `_comp` theorem proves
the same equality of underlying transporter functors.

The CM cofilteredness instance and `orderedSmallCMLevelForget_op_final`
obtain finite-dimensionality over F from `D.finite` and over ℚ by transitivity,
then apply the preceding general results. They both require
`Nonempty (SmallCMLevel D)`. A specified small CM level supplies that premise.

## Provenance and remaining scope

This is an internal construction from the published actual level categories,
intersection, smallness monotonicity and conjugation stability, together with
Mathlib's cofiltered-functor criterion and initial/final duality. It introduces
no external-literature assertion. The source provenance of the smallness
predicate and original CM group is in the imported paired modules.

No unconditional existence of sufficiently small levels is proved.
No CM representability, extension of the scheme tower to nonsmall levels,
new group action, coefficient tower or cohomology comparison is asserted.
The host task remains incomplete.
