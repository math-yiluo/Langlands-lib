# Higher direct images and restriction to an open of the base

Authors: Worker 727 and Worker 1013. Worker 1013 requested the comparison and
the vanishing interface for the reverse affine base-change proof (task
7584bcbd).

Module `Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`. Take a morphism
of schemes `f : X ⟶ Y`, an open `V` of `Y` and an `𝒪_X`-module `M`. The module
proves that the higher direct images of `M|_{f⁻¹ V}` along `f ∣_ V` are the
restrictions to `V` of the higher direct images of `M` along `f`:

`Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V}) ≅ (Rⁿ f_* M)|_V` for every `n`.

Everything is proved in the file. There are no hypotheses beyond those in the
signatures and no proof holes.

## Conventions

All schemes are in one universe `u`. Write `h_*` for Mathlib's
`Scheme.Modules.pushforward h`. For an open immersion `j`, write `ρ_j` for
Mathlib's `Scheme.Modules.restrictFunctor j`. Write `ρ_V` for `ρ_{V.ι}` and
`ρ_{f⁻¹ V}` for `ρ_{(f ⁻¹ᵁ V).ι}`. `M|_{f⁻¹ V}` is `ρ_{f⁻¹ V} M`. `Rⁿ h_*` is
the Library's `higherDirectImage h n`, defined as
`(Scheme.Modules.pushforward h).rightDerived n`. `f ∣_ V : f ⁻¹ᵁ V ⟶ V` is
Mathlib's `morphismRestrict`.

## Declarations

- `isZero_rightDerived_succ_of_preservesHomology F N q` (general abelian
  categories): if `F : A ⥤ B` is additive and preserves homology, and `A` has
  injective resolutions, then `(F.rightDerived (q + 1)).obj N` is zero.
- `additive_restrictFunctor j` (instance): `ρ_j` is additive for every open
  immersion `j`. It is transported along Mathlib's
  `restrictFunctorIsoPullback j : ρ_j ≅ j^*`, and `j^*` is additive.
- `preservesHomology_restrictFunctor j`: `ρ_j` preserves homology. It preserves
  finite limits by the Library's
  `OpenCohomologyVanishing.preservesFiniteLimits_pushforward`, and it preserves
  epimorphisms because it is a left adjoint.
- `restrictPushforwardOpensIso f V` (a `def`): for each open `W` of `V`, the
  equality of opens `f⁻¹ (V.ι '' W) = (f⁻¹ V).ι '' ((f ∣_ V)⁻¹ W)` of `X`
  (Mathlib's `image_morphismRestrict_preimage`). These equalities are assembled
  into a natural isomorphism of functors on opens,
  `V.ι.opensFunctor ⋙ Opens.map f.base ≅ Opens.map (f ∣_ V).base ⋙ (f ⁻¹ᵁ V).ι.opensFunctor`.
- `restrictPushforwardIso f V` (a `def`): the natural isomorphism
  `ρ_{f⁻¹ V} ⋙ (f ∣_ V)_* ≅ f_* ⋙ ρ_V` of functors `X.Modules ⥤ V.Modules`.
  Both sides are pushforwards along composite functors of opens. They are
  identified with Mathlib's `SheafOfModules.pushforwardComp` and compared along
  `restrictPushforwardOpensIso` with `SheafOfModules.pushforwardCongr₂`. The
  ring-map side condition reduces to Mathlib's `Scheme.Hom.appLE_map` and
  `Scheme.Hom.appLE_eq_app`.
- `isZero_rightDerived_restrictFunctor f V M q`: the right derived functors
  `R^{q+1} ρ_{f⁻¹ V}` vanish at `M`. This is the first lemma applied to
  `ρ_{f⁻¹ V}`.
- `isZero_higherDirectImage_restrict_of_injective f V J q`: for an injective
  `𝒪_X`-module `J`, `R^{q+1} (f ∣_ V)_* (J|_{f⁻¹ V})` is zero. `J` is flasque
  (`PushforwardInjectiveAcyclic.isFlasque_of_injective`), so `J|_{f⁻¹ V}` is
  flasque (`OpenCohomologyVanishing.isFlasque_restrict`). Flasque modules have
  vanishing higher direct images (`isZero_higherDirectImage_of_isFlasque`).
- `higherDirectImageRestrictIso f V M n` (a `def`): the isomorphism
  `Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V}) ≅ ρ_V (Rⁿ f_* M)`. It is the composite of two
  isomorphisms:
  1. The inverse of the Library's `compComparison` for
     `e = restrictPushforwardIso f V`, with `F = ρ_{f⁻¹ V}`,
     `G = (f ∣_ V)_*` and `H = f_* ⋙ ρ_V`. This is
     `Rⁿ (f ∣_ V)_* (ρ_{f⁻¹ V} M) ≅ Rⁿ (f_* ⋙ ρ_V) M`. It is an isomorphism by
     the Library's `isIso_compComparison`. Its hypotheses are the two lemmas
     above: `F` has vanishing higher derived functors at `M`, and `F` sends
     injectives to `G`-acyclic modules.
  2. The component at `M` of the Library's
     `LeftExactHomology.derivedNatTrans ρ_V f_* n :
     Rⁿ (f_* ⋙ ρ_V) ⟶ Rⁿ f_* ⋙ ρ_V`. Because `ρ_V` preserves homology, it is an
     isomorphism by `LeftExactHomology.isIso_derivedNatTrans`.
- `isZero_higherDirectImage_restrict_of_isZero_restrict f V M n hM`: if
  `ρ_V (Rⁿ f_* M)` is zero, then `Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V})` is zero.
- `isZero_higherDirectImage_restrict f V M n hM`: if `Rⁿ f_* M` is zero, then
  `Rⁿ (f ∣_ V)_* (M|_{f⁻¹ V})` is zero.
- `isZero_higherDirectImage_pullback f V M n hM`: the same conclusion for the
  pullback `((f ⁻¹ᵁ V).ι)^* M` in place of `M|_{f⁻¹ V}`. The two are isomorphic
  by Mathlib's `restrictFunctorIsoPullback`.

## Provenance

This is internal infrastructure. It is the standard fact that higher direct
images are compatible with restriction to an open subscheme of the target, so
that `Rⁿ f_*` is local on the target. No literature statement is formalized as
such. The proof uses only the Library's comparison theorems for derived
functors (`compComparison`, `LeftExactHomology.derivedNatTrans`), the vanishing
of higher direct images of flasque modules, and Mathlib's pushforward and
restriction functors.
