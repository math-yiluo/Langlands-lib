# Actual right-module fixed-source Hom functors

This is an internal additive construction for arbitrary associative nonunital rings. It packages the published original right-module Hom, residual action and postcomposition maps without changing the fixed source or its actions. The construction supports the right-module adaptations explicitly invoked in Renard I.4.2; it does not formalize the coefficient-linear tensor-dual comparisons in that section.

## Sources and provenance

The governing source is Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- Printed pp.5–7 / PDF11–13 specify commuting left/right bimodule actions, allow nonunital rings and nonunital modules even over unital rings, define idempotented rings and idempotent fixation, and introduce nondegenerate right modules.
- I.2.3, printed pp.16–18 / PDF22–24, constructs Hom functors, their nondegenerate parts, and the pseudo-forgetful and induction specializations for complex algebras.
- I.4.2, printed pp.23–24 / PDF29–30, explicitly invokes the analogous functors for right modules in its tensor-duality comparisons.

The relevant registered supplementary errata `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF1–2 and PDF18–19, were also consulted. Those pages do not supply the missing coefficient compatibility for the I.4.2 comparisons. The arbitrary-ring additive generality and the explicit interfaces below are internal derived infrastructure. The implementation adapts the published left-module `NondegenerateHomFunctor` pattern and reuses `NonUnitalBimoduleHomActions`, `NonUnitalBimoduleHomNaturality`, `NondegenerateModuleAdditive` and `NonUnitalModuleDualFixedPartMaps` by their Lean names.

## Ambient construction

Let `R` and `S` be nonunital rings, and let `Y` have its supplied additive group, left `R`-action and right `S`-action, with `hY : ActionsCommute R S Y`. Right actions are encoded as modules over the opposite ring. A variable `M` requires only its additive group and right `S`-action.

`ambientFunctor hY` sends `M` to exactly `rightSourceHom hY M`: its carrier is `NonUnitalModuleHom S.op Y M`, its group is the published pointwise Hom group, and its module structure is exactly `rightSourceAction hY`. For `r : R`, its entire scalar endomorphism is `precomposeAddHom (hY.leftActionHom r)`, and evaluation gives

```text
(op r • h)(y) = h(r • y).
```

`ambientMap hY f` is exactly `rightSourceMap hY hY (NonUnitalBimoduleHom.id R S Y) f`. Its entire additive map is `postcomposeAddHom f`, its Hom value is `f.comp h`, and evaluation is `f(h(y))`. The identity and composition laws are definitional equalities of whole original right-`R`-linear maps. Zero and addition use Hom extensionality twice and pointwise reflexivity. These laws package the actual additive ambient functor. No left action on the variable module, unit law, coefficient action, idempotentedness, or nondegeneracy is assumed.

## Actual nondegenerate part

With only `hR : IsIdempotented R`, `homPart hY hR M` abbreviates the published `nondegeneratePart hR.op (rightSourceHom hY M)`. It retains the inherited subgroup and module structure. `mem_homPart` states fixation by an actual `Idempotent R.op` under the named residual action. `mem_homPart_iff` gives the source notation

```text
h belongs to homPart iff there exists e : Idempotent R,
  for every y : Y, h((e : R) • y) = h(y).
```

The forward proof unops the actual idempotent and applies evaluation to the fixation equality. The reverse proof uses the published `NonUnitalModuleDualFixedPartMaps.oppositeIdempotent` and Hom extensionality. There is no assumption that the whole ambient Hom is nondegenerate.

`partMap` is exactly `ambientMap` restricted by `NonUnitalModuleHom.restrictNondegeneratePart`; its additive-map interface exposes that entire restriction, and its subtype value is `f.comp h.val`. Identity, composition, zero and addition reuse the published restriction laws and the corresponding ambient laws, as equalities of whole module maps.

`nondegenerateFunctor hY hR` is definitionally the composite `ambientFunctor hY ⋙ nondegeneratePartFunctor hR.op`. Its bundled object uses `nondegeneratePart_isNondegenerate hR.op`. Its object, carrier, group, action and maps are exposed explicitly. `restrictedFunctor` precomposes this with `nondegenerateInclusion S.op`; its whole-functor equality and object/map interfaces retain those exact data. Both functors are additive by the published composition, part and inclusion instances. Neither construction requires `IsIdempotented S` or nondegeneracy of `Y` or of the input ambient module.

## Natural inclusion and universes

`inclusion` is the left whiskering of `nondegeneratePartInclusion hR.op` by the ambient functor. Its complete component is `(homPart hY hR M).subtype`, its additive map is the subgroup inclusion, and its value is `h.val`. `restrictedInclusion` is the further whiskering by the input inclusion. Both expose these whole components and subtype formulas. Naturality is an equality of whole original right-`R`-linear maps; the unbundled equality permits different input and output carrier universes and follows by module-map extensionality and reflexivity.

The ring universes `uS`, `uR`, fixed-source universe `uY` and variable-carrier universe `uM` are independent. Hom carriers and output objects live in exactly `max uY uM`. Unbundled maps and composition also allow independent `uN` and `uP`. The companion `NondegenerateRightHomFunctorChecks` checks the complete unapplied interfaces, unequal small universes, competing supplied structures, subsingleton cases, and meaningful integer degenerate and regular cases.

The separate `RenardRightHomFunctors` unit specializes this construction on the original carrier `B` with explicitly selected regular actions. Coefficient recovery and linearity, source coefficient conventions, tensor-dual comparison maps and inverse identities, natural isomorphisms, adjunctions and exactness remain separate obligations. In particular this additive construction does not settle which coefficient compatibility I.4.2 intends or replace the existing residual coefficient adapter work.
