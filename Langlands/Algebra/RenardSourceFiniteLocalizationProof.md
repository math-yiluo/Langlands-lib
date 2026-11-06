# Proof: Renard C.II under each candidate finiteness reading

Worker 709 supplied the proof draft; Worker 1581 checked its source correspondence,
compiled the theorem, and prepared this submission. This module proves
`Langlands.Renard.SourceFiniteLocalization.SourceFiniteLocalizationStatements`
from `Langlands.Algebra.RenardSourceFiniteLocalizationStatements`. The
statement Markdown records the source passage (Renard 2026, C.II, printed
p.279 / PDF285) and the three readings; this file describes the implemented
Lean proof. Universes `uB` and `uV` stay independent, and no hypothesis is
added.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1581 reread printed p.6 / PDF12, printed pp.248–249 / PDF254–255,
and printed p.279 / PDF285; the final proposition on PDF285 was also
inspected visually. The statement's paired Markdown specifies the exact
source-to-Lean correspondence.

The three readings and the categorical comparisons below are internal derived
formulations. This proof establishes all three without selecting the author's
intended nonunital finiteness convention. It uses the published unitization,
Noetherian localization, and stable-image proofs; it does not follow Renard's
argument through finiteness of the endomorphism module and an integral equation
for the inverse localized operator. It asserts no coverage of other C.II results.

## Subobjects in `ActionModuleCat`

For `k : Type u` a commutative ring, `B : Type v` a nonunital ring with
`Module k B`, and `M : ActionModuleCat.{u,v,w} k B`, the proof builds the
helper order isomorphism

```lean
subobjectOrderIso M : Subobject M ≃o CompatibleSubmodule M.action
```

between the actual categorical subobjects of `M` and its stable
`k`-subspaces.

- `subObject M S` is `ActionModuleCat.of S.toSubmodule S.restrictAction`.
  `subArrow M S` is the published `S.subtypeIntertwiner`, which is a
  monomorphism by evaluation (`subArrow_mono`).
- `injective_of_mono`: the underlying map of a monomorphism `f` is
  injective. Compare the inclusion of the kernel object `subObject N f.hom.ker`
  with the zero intertwiner out of it. Both have composite zero with `f`,
  so they are equal by `cancel_mono`, and every kernel element is zero.
- `isoOfBijective` turns a bijective intertwiner into an isomorphism. Its
  inverse is the inverse linear equivalence; the inverse intertwines the
  actions because `f` is injective.
- The inverse order isomorphism sends `S` to `Subobject.mk (subArrow M S)`;
  `subobjectOrderIso M` sends a subobject `P` to `P.arrow.hom.range`. Going from `S` and back recovers
  `S` because `(mk f).arrow` is `underlyingIso f` followed by `f`. Going
  from `P` and back uses `Subobject.eq_mk_of_comm`, with the isomorphism
  given by `isoOfBijective` of the published `rangeRestrict` of the
  injective arrow. For the order, `S ≤ T` gives `Subobject.mk_le_mk_of_comm`
  through the published `codRestrict` of the inclusion; conversely
  `Subobject.ofMkLEMk_comp` places every element of `S` in `T`.

Under `[IsScalarTower k B B] [SMulCommClass k B B]`, composing with the
published `CompatibleUnitization.submoduleOrderIso` and the inverse of
Mathlib's `ModuleCat.subobjectModule` gives `unitizedSubobjectOrderIso M`
with the subobjects of `ModuleCat.of (Unitization k B) M`. That module uses
the published `CompatibleUnitization.module M.action`. The published
transport lemmas
`NonUnitalModuleFiniteness.hasFiniteSubcoverProperty_congr` and
`isNoetherianObject_congr` then give:

- `finiteType_iff_finite`: `IsFiniteTypeObject M` iff `M` is a finite
  unitized module. This composes the published
  `finiteTypeFiniteSubcover` with
  `ModuleFiniteType.finiteSubcover_iff_finite`.
- `noetherianObject_iff_isNoetherian`: `IsNoetherianObject M` iff `M` is a
  Noetherian unitized module, by the published
  `ModuleNoetherian.object_iff`.

## The three readings

`sourceConclusion_of_stabilization` turns the published
`CompatibleLocalizationStabilizationAt ρ f` into `SourceConclusion ρ f`. Its
positive stable exponent gives `EventuallyStable`. The published
`CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable`
supplies the stable-image clause for every positive stable exponent.

- `additiveReading`: install the three ambient actions
  `NonUnitalModule.ofLinearEndHom` locally. The published
  `NonUnitalModuleFiniteness.noetherianObject_iff_original_stable_generators`
  and `finiteType_iff_original_stable_generators` turn the categorical
  hypotheses into finite stable generation among stable additive subgroups.
  Each stable `AddSubgroup` becomes a `NonUnitalSubmodule` with the same
  carrier. The published `additiveIdealFiniteLocalization` then gives the
  stabilization.
- `compatibleReading`: `noetherianObject_iff_isNoetherian` makes `B`
  Noetherian over `Unitization ℂ B` for the regular action. The published
  `UnitizationIdealNoetherian.noetherian_iff_scalar_and_regular`, with the
  Noetherian field `ℂ`, makes `Unitization ℂ B` a Noetherian ring.
  `finiteType_iff_finite` makes the source and the localization finite
  unitized modules, and the published `stabilizationAt_of_finite`
  concludes.
- `unitizationReading` applies `stabilizationAt_of_finite` directly.

`sourceFiniteLocalizationStatements` is the conjunction of the three
theorems.

## Checks

A development Lake build compiled the proof module with zero errors and zero
warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. It inspected
`sourceFiniteLocalizationStatements` at levels `uB`, `uV`, with axioms
`propext`, `Classical.choice` and `Quot.sound` only. There are no proof holes or new axioms. These development checks do not
replace independent semantic review or publication.
