# Finite-covering trace on full equivariant locally constant sheaves

This internal construction extends the existing literal finite-fiber trace to
the entire ordinary-open moving-space equivariant locally constant sheaf.
It constructs a morphism

`f_* LC_X(ρ) ⟶ LC_Y(ρ)`

for an actual continuous equivariant finite covering map, naturally in every
original coefficient representation and intertwiner. The direct image and both
sheaves are the existing constructions in `DirectImage` and
`LocallyConstantSheaf`; they retain every ordinary open and every group label.

## Inputs and size conventions

The spaces `X`, `Y`, and, for composition, `Z` have a common arbitrary universe
`u`, as in the existing direct-image functor. The acting group has independent
universe `v`; the commutative ring has universe `r`, and coefficient modules have
universe `w`. Section modules have universe `max u w`. The group is abstract:
each constant spatial action map is continuous, and no topology on the group or
on the coefficients is needed. Coefficients range over the entire `Rep R G`,
with all linear intertwiners, arbitrary dimension, and no smoothness premise.

The original map is `f : C(X,Y)` with its original equivariance equation.
Its fibers are finite, and `IsCoveringMap f` supplies actual evenly covered
charts. Surjectivity is not required by this Mathlib predicate; empty fibers
are allowed and contribute zero. No properness or compact-support premise is
needed for this full sheaf construction.

## Fiber constructions and restriction naturality

`pointMapFiberEquiv` identifies the fiber of the existing restricted map
`pointMap f hf U : f⁻¹(U) → U` over `y : U` with the entire original
fiber `f⁻¹{y.val}`. Both maps retain the same underlying point. It supplies
`pointMap_finiteFiber`. `pointMap_isCoveringMap` uses Mathlib's actual restriction
of the covering map to the inverse image of a subset.

For every labelled arrow `k : U ⟶ V`, `labelledPointMapFiberEquiv` sends a
point in the restricted fiber over `y` to `k.label • x` in the restricted
fiber over `k.label • y`. Its inverse acts by `k.label⁻¹`. Original
equivariance and the group inverse laws prove membership and both inverse laws.
This works for arbitrary labelled arrows, including those that are not ordinary
inclusions and labels whose underlying spatial action is not faithful.

`trace_restriction` reindexes the finite sum by this equivalence, commuting
`ρ(k.label⁻¹)` with the sum. It proves compatibility with the existing
restriction maps, whose coefficient operator is precisely this inverse
label. The restriction equation is a consequence of the construction, not
additional input.

## Sheaf trace, coefficients, and intrinsic laws

`coefficientTrace` uses the existing `traceLinearMap` on every inverse-image
open. The proved restriction law makes these maps a morphism of the full
ordinary-open equivariant module sheaves. `coefficientTrace_apply` records its
literal restricted-fiber sum. `coefficientTrace_apply_sum` reindexes this
formula over every point of the original fiber of `f`; a `Fintype` on that fiber
only expresses the finite sum and can always be obtained from the finiteness
premise.

`coefficientTrace_pullback_apply` proves that coefficient pullback followed by
trace sends `s` at `y` to `Nat.card (f⁻¹{y.val}) • s y`. The multiplier is the
cardinality of the original fiber, and multiplication is natural-number scalar
multiplication in the additive coefficient group. Neither constant degree nor
division by degree is assumed.

`coefficientTraceNatTrans` packages trace as a natural transformation from
`LocallyConstantSheaf.functor R G X ⋙ sheaf f hf _` to
`LocallyConstantSheaf.functor R G Y`. Its proof uses `trace_map`, so every
original coefficient intertwiner is preserved.

`coefficientTrace_id` and `coefficientTraceNatTrans_id` give the identity for the
actual one-sheeted identity covering, with its finite fibers constructed from
`finite_id_fiber`. `coefficientTrace_comp` and
`coefficientTraceNatTrans_comp` compare trace for `g.comp f` with the direct
image of trace for `f` followed by trace for `g`. The proof partitions each
restricted composite fiber by `compFiberEquiv` through `fiberSum_comp`.
Finiteness of fibers of `f`, `g`, and their composite is explicit, with composite
finiteness also available from `finite_comp_fiber`. Covering of the composite is
an explicit premise; no closure theorem for arbitrary covering composition is
assumed.

## Provenance and remaining scope

This is a derived internal construction from the existing full locally constant
equivariant sheaf, ordinary direct image, and finite-covering trace. The original
covering charts prove local constancy of the sum; the explicit original-fiber
equivalences prove the new restriction and degree laws. Identity and composition
use the existing finite-sum laws. No external literature theorem is represented
as established.

This module does not construct an etale or Godement trace, a higher derived
trace, a smooth direct-image trace, an arithmetic Hecke correspondence, or a
Harris comparison. It does not instantiate a rational or Shimura covering.
Those specializations and comparisons remain separate obligations of the
broader task.
