# The chosen local-module functor and its Mathlib comparison

Author: Worker 1570. This internal construction makes the published chosen
module localizations functorial and compares them with the specified Mathlib
localization functor. All declarations are in
`Langlands.Renard.ModuleLocalization`.

## Provenance and scope

The motivating original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix A.III.1,
printed pp.251–252 / one-based PDF257–258, especially example 4 on PDF258.
Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
That passage describes localization as a universal arrow into the full
subcategory of modules on which the denominators act invertibly, regarded
as modules over the original ring.

The present functors and their comparison are internal packaging of that
example and the published actual constructions. They are not a further
literal theorem asserted in the passage. The implementation imports
`RenardLocalModuleCategory`, hence `RenardModuleLocalization`, and retains
their objects, canonical arrows, locality predicate and scalar actions.
The false scalar-inverse parenthesis discussed in those paired files and
`notes/renard/appendix-a-corrections.md` is not used: locality means that
each denominator acts by an invertible module endomorphism.

The implementation uses Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, principally
`Algebra/Category/ModuleCat/Localization.lean`,
`Algebra/Category/ModuleCat/Ulift.lean`,
`Algebra/Category/ModuleCat/ChangeOfRings.lean` and
`RingTheory/Localization/Module.lean`.
Worker 709 specified the target interface and recorded its feasibility in
the task context; the present implementation does not reuse the private
probe. The imported published constructions retain their own authorship.

This file supplies functorial data and its intrinsic laws. It does not
assert an adjunction or source-sequence exactness for the chosen functor.
The restricted polynomial-module/endomorphism equivalence, the subsequent
chosen endomorphism-arrow comparison and their separate publication gates
are unchanged.

## Carriers and universes

Let `R : Type u` be any commutative unital ring, `S : Submonoid R`, and
`M : ModuleCat.{v} R`. The ring, module-carrier and enlargement universes
`u`, `v`, `w` are independent; write `κ = max u v w`.

| Construction | Actual carrier or category |
| --- | --- |
| `sourceRaisingFunctor.obj M`, abbreviated U(M) below | `ULift.{max u w} M`, in `ModuleCat.{κ} R` |
| `chosenLocalFunctor.obj M`, abbreviated F(M) | Exactly `canonicalLocalObject.{u,v,w} S M`, with carrier `ULift.{w} (LocalizedModule S M)` |
| `mathlibLocalizationFunctor.obj M`, abbreviated G(M) | `Shrink.{κ} (LocalizedModule S (ULift.{max u w} M))`, with the R-action restricted from `Localization S` |
| `mathlibLocalFunctor.obj M`, abbreviated GLocal(M) | The same G(M), equipped with its proved `IsSLocal S` property |

Here `LocalizedModule S M` is the actual Mathlib quotient of pairs, of
universe `max u v`. Both F and GLocal target the published
`LocalModuleCat.{u,κ} S`, the full subcategory of actual R-modules with
property `IsSLocal S`. Every ambient R-linear map between its objects is
a morphism.

U is exactly `ModuleCat.uliftFunctor.{max u w,v} R`.
`sourceRaisingFunctor_obj` identifies its object with `raisedSource M`;
`sourceRaisingFunctor_map_apply` and `sourceRaisingFunctor_map_up`
identify its map with `ULift.up ∘ f ∘ ULift.down`.

G is definitionally the specified composite

```text
U ⋙ ModuleCat.localizedModuleFunctor.{κ} S ⋙
  ModuleCat.restrictScalars (algebraMap R (Localization S)).
```

The `Small.{κ} R` instance required by Mathlib is synthesized internally,
since κ includes u. It is not an additional premise. No nontriviality,
nonzero-denominator, cardinality, faithful-action, domain, finite-generation
or dimension assumption occurs. The constructions and laws also apply to
the zero ring, zero modules and submonoids containing zero.

## Actual maps and canonical natural transformations

`chosenLocalMap S f` wraps the ambient R-linear map

```text
ULift.moduleEquiv.symm ∘
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f.hom ∘
  ULift.moduleEquiv.
```

The rightmost equivalence removes the source localization lift and the
leftmost restores the target localization lift.
`chosenLocalMap_hom` records this exact underlying linear map.
`chosenLocalMap_up_mk` proves, for every m and denominator s,

```text
ULift.up (LocalizedModule.mk m s) ↦
  ULift.up (LocalizedModule.mk (f m) s).
```

`chosenLocalMap_id` and `chosenLocalMap_comp` follow by quotient
representative induction and this formula. They provide the functor laws
of `chosenLocalFunctor`. Its `_obj` and `_map` lemmas expose the exact
published object and the map just constructed.

`chosenLocalizationUnit : U ⟶ F ⋙ localModuleInclusion S` has exactly
`canonicalModuleMap S M` as its component, as recorded by
`chosenLocalizationUnit_app`. Its naturality is proved by evaluating at
`ULift.up m` and applying the representative formula at denominator 1.
`chosenLocalizationUnit_naturality` states that square with the named
canonical maps.

The native R-action on Mathlib's Shrink localization and the action
obtained by restriction from `Localization S` are treated explicitly.
For any `P : ModuleCat.{max u v} R`, `mathlibActionEquiv S P` is an
R-linear equivalence from `P.localizedModule S` with its native R-action
to the same carrier with its restricted action. Both functions are the
identity. Its scalar law is proved using
`IsScalarTower.algebraMap_smul`, giving

```text
r •native z = (algebraMap R (Localization S) r) • z = r •restricted z.
```

`mathlibActionEquiv_apply` exposes the identity function.
`mathlibCanonicalMap S M` composes the native
`(U.obj M).localizedModuleMkLinearMap S` with this explicit equivalence.
Thus it is linear for the actual target action of G(M).
`mathlibCanonicalMap_apply` identifies its function exactly with that
Mathlib canonical map. `mathlibCanonicalMap_isLocalizedModule` transports
Mathlib's localization instance along the action equivalence.
`mathlibLocalizationFunctor_isSLocal` then uses
`IsLocalizedModule.map_units` to prove locality for the restricted action.

`mathlibLocalFunctor` is the `ObjectProperty.lift` of G by this locality
proof. Its `_obj` and `_map` lemmas identify both ambient components, and
`mathlibLocalFunctor_comp_inclusion` identifies the whole composite with G.
`mathlibLocalizationUnit : U ⟶ G` has components
`mathlibCanonicalMap S M`. Its naturality uses the actual
`IsLocalizedModule.map_apply` formula on canonical images; the `_app` and
`_naturality` lemmas expose these components and squares.

## Explicit natural comparison

`localizationRaisingEquiv S M` localizes the R-linear equivalence
`M ≃ₗ[R] ULift.{max u w} M`. It uses `IsLocalizedModule.mapEquiv` over
`Localization S` and then restricts scalars to R.
`localizationRaisingEquiv_mk` proves that it sends `mk m s` to
`mk (ULift.up m) s`.

`chosenMathlibLinearEquiv S M` is the following actual R-linear
equivalence:

1. Remove the chosen localization's outer ULift.
2. Apply `localizationRaisingEquiv`.
3. Apply `Shrink.linearEquiv R ...` in the inverse direction.
4. Apply `mathlibActionEquiv` to reach the actual restricted action.

Its `_up_mk` lemma proves the exact function

```text
ULift.up (LocalizedModule.mk m s) ↦
  (Shrink.linearEquiv R
    (LocalizedModule S (ULift.{max u w} M))).symm
      (LocalizedModule.mk (ULift.up m) s).
```

`chosenMathlibLinearEquiv_comp` proves that composing the published
`canonicalModuleMap S M` with this equivalence gives exactly
`mathlibCanonicalMap S M`. It evaluates the representative formula at
denominator 1.

`canonicalModuleMap_isLocalizedModule` proves a localization certificate
for the actual raised canonical arrow by transporting the existing
quotient localization certificate along the source and target ULift
linear equivalences. No universal-property certificate is assumed.

`chosenMathlibIso : F ≅ GLocal` bundles the displayed linear equivalences
as full-subcategory isomorphisms and uses `NatIso.ofComponents`.
For naturality, `IsLocalizedModule.ext` reduces equality of the two
actual maps out of F(M) to equality after the actual canonical arrow.
On `ULift.up m`, the representative formulas and the proved Mathlib-unit
naturality give the required equality. This proves naturality for every
R-linear morphism.

The following intrinsic laws expose the bundled result:

- `chosenMathlibIso_hom_up_mk`: the displayed denominator formula.
- `chosenMathlibIso_canonical`: the exact equation
  `canonicalModuleMap S M ≫ inclusion.map (α.hom.app M) = ηMathlib.app M`.
- `chosenMathlibIso_naturality`:
  `F.map f ≫ α.hom.app N = α.hom.app M ≫ GLocal.map f`.
- `chosenMathlibIso_hom_inv` and `chosenMathlibIso_inv_hom`: both component
  inverse laws, obtained from the actual natural isomorphism.

Consequently the comparison identifies the actual maps as well as the
chosen object carriers and their canonical localization arrows.
