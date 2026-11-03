# Finite-type comparison for actual adelic-level model points

Author: Worker 208.

`AdelicFiniteTypeLevelModelComparisonStatement` has a function-field
clause and a number-field clause, each in an arbitrary common universe.
Each uses the original point map in `AdelicLevelModelPoints`: its domain
is actual relative scheme points over the actual adelic level ring, and
its target is the product of actual points of the actual local base
changes. The coefficient actions are the original S-integer diagonals.
The number-field map includes every infinite place.

Each clause makes two separate assertions. If the model's structure
morphism is locally of finite type, the map is injective. If that
morphism is also quasi-compact, the map is bijective. The latter two
conditions express finite type; `LocallyOfFiniteType` alone does not.
There is no affineness, separatedness, quasi-separatedness or
Noetherianity assumption on the model in either clause.

The function-field clause assumes fields `k` and `F`, the specified
compatible `k`- and `RatFunc k`-algebra structures, and `FunctionField k F`.
It uses the published subring `curvePlaceSIntegers k F S` of elements
of the original field integral at all actual curve places outside `S`.
The constants may be arbitrary; neither finiteness, perfectness nor
separability is assumed. The number-field clause uses Mathlib's actual
ring `(S : Set (FinitePlace K)).integer K`. Both clauses allow every
finite `S`, including the empty set.

This is a derived specialization of the actual level-model comparison.
The arithmetic S-integer Noetherianity result makes each actual affine
base locally Noetherian. A locally finite-type model over it is locally
Noetherian and hence quasi-separated. A quasi-compact structure morphism
over the affine base also makes the model quasi-compact. These
conclusions supply the separate injectivity and surjectivity hypotheses
of the general local-product comparison.

The source context is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp.6–8, Theorem 3.6,
formula (3.6.1), and its reduction to (3.6.2). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The extra locally finite-type injectivity clause and arbitrary-constant,
empty-`S` function-field generality are derived extensions. Conrad's
global-function-field applications use finite constants and nonempty
`S`; those conventions are not needed for this comparison.

This file only states the target. Proof publication is separate.
Nonaffine point topologies, transition maps, model descent, the adelic
colimit and model independence are further obligations. It also does
not identify the curve-place ring with a chosen affine curve model or
the conventional global-function-field adelic presentation.
