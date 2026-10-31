# The actual coordinatewise completion functor

Authors: Worker 6 (construction, proofs and interface checks) and
Worker 734 (audit against the source and objective; added the
nondegenerate object-action and whole-component lemmas and their
interface checks). The governing source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Chapter I conventions and I.1.1–I.1.5, printed
pp.5–11/PDF11–17. The registered source identifier is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The family carrier is described at printed p.9/PDF15, and the original
left action and coordinatewise functor formula at printed p.10/PDF16.

## Scope and provenance

Renard defines completion on nondegenerate modules over an idempotented
ring and sends an intertwiner `f` to the map whose `e` coordinate is
`f (x(e))`. This module implements that formula on the actual
`NonUnitalModuleLeftLimit` carriers and their named original actions.
`nondegenerateModuleCompletionFunctor` has precisely the source's
nondegenerate input category and ambient output category.

The extension to all original ambient modules, the explicit universe
bounds, the additive Hom packaging and the natural transformation at a
saturated universe are internal generalizations. Their proofs are given
in the Lean file. The coordinate additive construction needs no finite
local units or nondegeneracy. Equivariance for the constructed family
actions and the bundled functors require exactly
`hA : IsIdempotented A`. No unit-action law, commutativity,
nontriviality or nondegeneracy of an ambient input is assumed.
Zero rings, zero actions and trivial carriers remain allowed. The named
original actions are retained even when their carrier types coincide
with the scalar ring's type.

The imported `NonUnitalModule`, `NonUnitalModuleAdditive` and
`NondegenerateModuleAdditive` interfaces supply the actual categories,
original intertwiners and pointwise Hom groups. The family carrier,
action and canonical intertwiner come from
`NonUnitalModuleLeftLimitAction` and its imports. No replacement
category or assumed completion functor is introduced.

## Coordinate maps and their intrinsic laws

Inside `NonUnitalModuleLeftLimit`, `mapAddHom f` applies `f` to every
coordinate. For independently sized `A : Type uA`, `M : Type uM` and
`N : Type uN`, it has type

```text
NonUnitalModuleLeftLimit A M →+ NonUnitalModuleLeftLimit A N.
```

Its closure proof uses `f.map_smul`: fixed coordinates remain fixed,
and the left-coherence equation for `e ≤ d` passes through `f`.
`mapAddHom_fixed` and `mapAddHom_coherent` expose these equations;
`mapAddHom_val` gives the literal coordinate formula. Additivity follows
from the original additive map underlying `f`.

The identity, composition, zero, addition and negation laws
`mapAddHom_id`, `mapAddHom_comp`, `mapAddHom_zero`, `mapAddHom_add` and
`mapAddHom_neg` are equalities of entire additive maps. Their proofs
reduce by additive-map and family extensionality to the corresponding
coordinate expressions. `mapAddHomAddHom` packages additivity in `f`
using the published pointwise original-intertwiner group.

The existing canonical family sends `m` to `(e ↦ e • m)`.
`mapAddHom_canonical` proves naturality by applying `f.map_smul` at
`e`. `mapAddHom_comp_canonical` states the same result as an equality
of entire additive maps, still without `hA`.

## Original equivariance

`mapAddHom_scalarAction` proves that the actual additive map intertwines
the two named family actions. At coordinate `e` and scalar `a`, choose
one idempotent `d` with `(e*a)*d = e*a`, using `hA`. The imported
`scalarAction_val` formula computes both family actions using this same
right local unit. The remaining equation is

```text
f ((e*a) • x(d)) = (e*a) • f (x(d)),
```

which is the original equivariance of `f`. This proof preserves the
multiplication order and uses neither commutativity nor an original
unit law.

`mapHom hA f` retains `mapAddHom f` as its entire
`toAddMonoidHom` field and adds this equivariance proof. Its type
explicitly names the source and target `nonUnitalModule hA` actions.
`mapHom_toAddMonoidHom` and `mapHom_val` state the exact retained map
and its coordinates. The identity, composition, zero, addition and
negation laws for `mapHom` follow by original-intertwiner and family
extensionality. `mapHomAddHom` bundles the pointwise additivity.
`mapHom_comp_canonicalHom` proves naturality as an equality of the
actual original intertwiners, using the additive naturality above.

## Bundled functors and universe accounting

`nonUnitalModuleCompletionFunctor hA` has type

```text
NonUnitalModuleCat.{uA,uM} A ⥤
  NonUnitalModuleCat.{uA,max uA uM} A.
```

Its object at `M` is exactly `NonUnitalModuleLeftLimit A M`, with
`NonUnitalModuleLeftLimit.nonUnitalModule hA` installed as its original
action. Its map is exactly `mapHom hA f`. The named object, action,
map, underlying-additive-map and coordinate formulas expose these
choices. Functoriality uses the proved identity and composition laws.
`nonUnitalModuleCompletionFunctor_additive` uses `mapHom_add`, so the
Hom addition is the published pointwise operation.

`nondegenerateModuleCompletionFunctor hA` is the composite of the
published `nondegenerateInclusion A` with this ambient functor. Its
object is the actual family carrier of `M.obj` with the action
`NonUnitalModuleLeftLimit.nonUnitalModule (M := M.obj) hA`, and its map
extends `f.hom` by the same coordinate formula. The named object,
action, map, underlying-additive-map and coordinate equations are
definitional.
Its additive instance follows from additivity of inclusion and ambient
completion. The output is an ambient module; it is not asserted to be
nondegenerate.

The family carrier belongs to `Type (max uA uM)`, since its coordinates
are indexed by idempotents in `A`. The construction keeps that rise
explicit and requires no equality between the scalar and vector
universes. The unbundled maps allow independently sized source and
target carriers. Each bundled functor fixes one input carrier universe,
as do the imported categories.

## Canonical natural transformation and interfaces

At the saturated carrier universe `max uA uM`, completion is an
endofunctor because `max uA (max uA uM) = max uA uM`.
`nonUnitalModuleCompletionCanonical hA` bundles the existing
`canonicalHom hA` maps as a natural transformation from the identity
ambient functor to completion at this universe. Its naturality proof
is `mapHom_comp_canonicalHom` with the categorical composition
orientation. `nonUnitalModuleCompletionCanonical_app` states that each
component is exactly the original intertwiner `canonicalHom hA`; the
other two component lemmas expose its entire additive map and the
formula `m ↦ (e ↦ e • m)`.
For arbitrary independently sized carriers, the unbundled canonical
naturality equations above apply without changing their universes.

The file checks complete unapplied interfaces for the additive map,
original intertwiner, retained additive map, coordinate laws,
canonical naturality, both functors, additivity, exact bundled object,
action and map formulas, and the natural transformation and its
components.
The checks include arbitrary independent universes and both unequal
assignments `(uA,uM) = (0,1)` and `(1,0)`. The last examples explicitly
install the original zero action on the scalar ring's own carrier,
checking the additive map, retained Hom map, ambient object and
coordinate equivariance.

This unit supplies constructions and their intrinsic laws. Faithfulness,
nondegenerate-part recovery, the smoothing/completion adjunction,
topology, analytic completion and submodule closure remain separate
statement and proof units. It does not establish the proposition in
I.1.5 or complete I.1.4, I.1.5 or the whole-book program.
