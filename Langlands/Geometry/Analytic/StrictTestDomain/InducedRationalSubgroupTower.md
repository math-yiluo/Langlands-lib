# The original finite-index rational subgroup tower

This internal construction makes the finite-index open subgroups of one
original open subgroup into an actual geometric and cohomological tower.
Every level retains the same originally invariant rational presentation.
Every transition is the previously constructed subgroup restriction map,
with its original induced spectrum and full-group action. The construction
specializes the existing smooth proper transport diagrams; it does not take
a tower, cohomology objects or transition comparisons as new input data.

## Inputs and coefficient scope

The complete ultrametric normed field `K`, the presented strict affinoid
algebra `P`, and the topological group `G` share arbitrary universe `u`.
Fix an actual rational spectral action `ρ`, an open subgroup `U`, and an
originally `U`-invariant rational domain `d`. The geometric section assumes
`IsTopologicalGroup G`.

The smooth construction has one further premise:
`HasStableNeighbourhoods` for the original local spectrum at `U` with its
original `U` action. Local stability at every smaller level and full-group
stability on its induced spectrum are derived. Stability is not assumed
separately at each level.

The coefficient ring `R : Type u` is an arbitrary commutative ring.
All coefficient diagrams use the full original
`SmoothRep.{u, u, u} R G`, including every object and intertwiner. No
coefficient dimension, admissibility or additional coefficient topology is
imposed. The common universe follows the existing smooth proper transport
diagram interface.

## Original levels and geometry

`FiniteIndexLevel U` is the subtype of original open subgroups `V` such that
`V ≤ U` and `V.toSubgroup.relIndex U.toSubgroup ≠ 0`. It inherits its
inclusion order, hence Mathlib's thin category: a morphism `V ⟶ W`
records the original inclusion `V.val ≤ W.val`.

`base U` is the original subgroup `U`, with relative index one.
`commonRefinement V W` is the original intersection of the two open
subgroups. Mathlib's `Subgroup.relIndex_inf_ne_zero` proves its finite-index
condition, and the usual intersection inclusions give arrows to both
levels. The `IsCofiltered` instance uses this intersection cone;
equalization of parallel maps follows from the thin category. Thus the
level category is nonempty and cofiltered without any chosen replacement
family of subgroups.

`finite_relativeQuotient V W` proves that
`W.val ⧸ V.val.toSubgroup.subgroupOf W.val.toSubgroup` is finite.
This assertion needs no inclusion between `V` and `W`: both lie below `U`,
and `V` has finite relative index in `U`. The proof applies
`Subgroup.relIndex_eq_zero_of_le_right` contrapositively to obtain the
nonzero relative index in `W`, then
`Subgroup.index_ne_zero_iff_finite` supplies the quotient's finiteness.
In particular, every actual inclusion arrow has the finite relative
quotient needed by the original subgroup covering construction.

`rationalObject d V` restricts the original action and invariant domain
from `U` to `V.val`, then includes that object in the original rational
transport category. Restriction retains the rational presentation.
`rationalArrow d f` is exactly the existing label-one
`subgroupRestriction` for the inclusion represented by `f`.
`rationalTower` uses the original subgroup identity and composition
theorems to prove its functor laws.

For every arrow, the module proves that its actual induced continuous map
is a covering map, that every literal fiber is finite, and that the fiber
cardinality is precisely `V.val.toSubgroup.relIndex W.val.toSubgroup`.
It also proves properness of that original map. These assertions reuse the
original subgroup covering and fiber constructions, with the relative
quotient finiteness just derived. They require neither levelwise geometric
witnesses as extra inputs nor normality of the open subgroups.

`hasStableNeighbourhoods_local` restricts the sole largest-level local
stability premise along each original subgroup inclusion.
`hasStableNeighbourhoods_induced` then uses the existing spatial induction
construction to obtain stability on the actual induced spectrum with its
full `G` action. `smoothObject` and `smoothArrow` bundle precisely these
objects and proper original arrows in `SmoothProperTransport ρ`.
The `smoothTower` functor laws are reflected through its faithful
forgetful functor. `smoothTower_forget` is a definitional equality with
`rationalTower`; the smooth tower does not alter the underlying objects or
maps. `spectrumTower` records their original continuous full-group actions.

## Full coefficient and complex diagrams

Each cohomological tower is obtained by precomposing the corresponding
published `SmoothProperTransport` diagram with `(smoothTower d).op`.
It therefore retains both level naturality and all coefficient naturality.
The level variance is contravariant, since these transitions are proper
pullbacks.

- `compactFunctionsTower` uses the original compactly supported locally
  constant function representations. `invariantCompactFunctionsTower`
  applies whole-group smooth invariants.
- `godementCompactTower` uses the existing full compact smooth Godement
  complexes and their independently constructed proper chain maps.
  `godementInvariantCompactTower` uses termwise whole-group invariants.
  `godementInvariantCompactTowerIso` makes their existing comparison
  natural over the level category as well as coefficients.
- `godementCohomologyTower q` takes actual homology in the smooth
  representation category. `godementInvariantCohomologyTower q` instead
  takes module homology after termwise invariants.
- `godementInvariantsEdgeTower q` is the existing canonical edge between
  these two routes. It is an isomorphism in degree zero under the stated
  inputs. The all-degree isomorphism instance additionally assumes that
  `smoothInvariants R G` preserves homology.
  `godementInvariantsArrowTower q` retains the same edge squares as a
  functor to the actual arrow category.
- `compactDerivedZeroTower` and `invariantCompactDerivedZeroTower` use the
  existing sheaf-derived compact-section objects in degree zero and their
  previously constructed proper maps.

The last two towers have only degree-zero spatial maps. Their underlying
objects come from the actual right-derived functors on ordinary-open
equivariant coefficient sheaves. The all-degree Godement homology towers
do not identify those homology objects with sheaf-derived cohomology in
positive degree.

## Degree-zero comparisons and original transitions

Four isomorphisms identify Godement cohomology in degree zero and
sheaf-derived compact sections in degree zero, with and without
whole-group invariants, with the original corresponding compact-function
towers. Each is `Functor.isoWhiskerLeft` of the previously constructed
diagram isomorphism. The new module requires no comparison squares as
input.

`godementDerivedZeroTowerIso` and
`godementInvariantDerivedZeroTowerIso` compose these isomorphisms through
the same original compact-function tower. The final two
natural-transformation equalities prove that both composites preserve
that compact-function identification. Thus these are comparisons of
whole coefficient towers, not only objectwise isomorphisms.

`compactFunctionsTower_obj` identifies each object with its original
`CompactSections.coefficientFunctor`. `compactFunctionsTower_map`
identifies each level map definitionally with the original
`subgroupRestrictionCompactSupportPullbackNatTrans`. The functor laws
and comparisons therefore concern the existing subgroup pullbacks on
the original coefficients and functions.

## Provenance and remaining obligations

The provenance is internal. The level category and finiteness arguments
use Mathlib's original subgroup relative-index definitions and thin
category construction. Geometric arrows, their covering and fiber
theorems, stability restriction, subgroup transitivity, and the smooth
proper transport diagrams are reused by their Lean names. The remaining
construction is functor composition and whiskering; it assumes no
external Harris or Berkovich theorem.

This is the finite-index subgroup tower for one fixed invariant rational
presentation. It does not construct general rational coverings, analytic
or etale realization, Godement acyclicity or resolution exactness, higher
sheaf-derived spatial maps, higher derived traces, or a covariant trace
tower. It proves no unrestricted stability premise, arithmetic Hecke
identification, uniformization, Shimura specialization or Harris
compatibility. Those remain obligations of the broader framework.
