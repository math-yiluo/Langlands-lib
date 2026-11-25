/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.BaseChange
public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Blowup.Principalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!

# The blow-up of a pulled-back ideal is a closed subscheme of the base change

For a morphism of schemes `f : Y ⟶ X` and an ideal sheaf `I` on `X`, the blow-up of the
pulled-back ideal `I.comap f` maps to the fibre product `Y ×_X Bl_I(X)` via its
structure morphism and any lift `ρ : Bl_{I·O_Y}(Y) ⟶ Bl_I(X)` provided by the
universal property of the blow-up (Stacks Project Tag 0806; such a lift exists because
the pullback of `I` to `Bl_{I·O_Y}(Y)` is the invertible exceptional ideal, and it is
unique). We show that this canonical morphism is a **closed immersion** — the global
closed-immersion half of Stacks Project Tag 080E; the identification of its image with
the strict transform is in `WeilConjectures.Compactification.StrictTransformBlowup`.

The proof reduces to the affine case
`AlgebraicGeometry.AffineBlowup.isClosedImmersion_pullbackLift` over the opens of
`Y ×_X Bl_I(X)` spanned by an affine open `V ⊆ Y` lying over an affine open `U ⊆ X`
and the blow-up chart of `Bl_I(X)` over `U`, using that being a closed immersion is
Zariski-local on the target.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`

## Blueprint

Part of `thm:nagata-strict-transform-is-blowup` (Stacks Project Tag 080E),
closed-immersion half.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The blow-up chart over an affine open `U`, composed with the blow-up map, is the
structure morphism of the affine blow-up followed by `U.2.fromSpec`. -/
@[reassoc]
lemma blowupι_comp_blowupMap (I : X.IdealSheafData) (U : X.affineOpens) :
    I.blowupι U ≫ I.blowupMap = AffineBlowup.toSpec (I.ideal U) ≫ U.2.fromSpec := by
  rw [blowupι_blowupMap, blowupNatTrans_app]
  exact Category.assoc _ _ _

/-- **Chart compatibility of the lift.** Over an affine open `U` of `X` and an affine open
`V` of `Y` lying over `U`, the lift `ρ` restricted to the blow-up chart at `V` is the
functoriality morphism of affine blow-ups followed by the blow-up chart at `U`. This is an
instance of the uniqueness part of the universal property of the blow-up. -/
lemma blowupι_comp_of_le_preimage (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).blowupι V ≫ ρ =
      AffineBlowup.hom (f.appLE U.1 V.1 hVU).hom (I.ideal_comap_appLE f U V hVU).symm ≫
        I.blowupι U := by
  refine I.hom_ext_of_isInvertible_comap
    (t := (I.comap f).blowupι V ≫ (I.comap f).blowupMap ≫ f) ?_ ?_ ?_
  · rw [comap_comp, comap_comp]
    exact (isInvertible_comap_blowupMap (I.comap f)).comap_of_isOpenImmersion _
  · rw [Category.assoc, ← hρ]
  · rw [Category.assoc, I.blowupι_comp_blowupMap U, AffineBlowup.hom_toSpec_assoc,
      CommRingCat.ofHom_hom, IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 hVU,
      (I.comap f).blowupι_comp_blowupMap_assoc V]

/-- The affine comparison square attached to an affine open `V` of `Y` lying over an affine
open `U` of `X`, in the form in which the affine base-change theorem states it. -/
lemma specMap_ofHom_appLE_fromSpec (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    Spec.map (CommRingCat.ofHom (f.appLE U.1 V.1 hVU).hom) ≫ U.2.fromSpec =
      V.2.fromSpec ≫ f := by
  rw [CommRingCat.ofHom_hom]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 hVU

/-- **The affine chart of the fibre product.** For an affine open `U` of `X` and an affine
open `V` of `Y` lying over `U`, this is the induced open immersion from the fibre product of
`Spec Γ(Y, V) ⟶ Spec Γ(X, U)` and the blow-up chart of `Bl_I(X)` at `U` into `Y ×_X Bl_I(X)`.
-/
noncomputable def pullbackChart (I : X.IdealSheafData) (f : Y ⟶ X)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    pullback (Spec.map (CommRingCat.ofHom (f.appLE U.1 V.1 hVU).hom))
        (AffineBlowup.toSpec (I.ideal U)) ⟶ pullback f I.blowupMap :=
  pullback.map _ _ f I.blowupMap V.2.fromSpec (I.blowupι U) U.2.fromSpec
    (specMap_ofHom_appLE_fromSpec f U V hVU) (I.blowupι_comp_blowupMap U).symm

/-- The chart of the fibre product at `(U, V)` is an open immersion, being a base change of
open immersions along a monomorphism. -/
instance isOpenImmersion_pullbackChart (I : X.IdealSheafData) (f : Y ⟶ X)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    IsOpenImmersion (pullbackChart I f U V hVU) := by
  unfold pullbackChart
  infer_instance

/-- A point of `Y ×_X Bl_I(X)` lies in the chart at `(U, V)` exactly when its image in `Y`
lies in `V` and its image in `Bl_I(X)` lies over `U`. -/
lemma mem_opensRange_pullbackChart (I : X.IdealSheafData) (f : Y ⟶ X)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (p : ↥(pullback f I.blowupMap)) :
    p ∈ (pullbackChart I f U V hVU).opensRange ↔
      pullback.fst f I.blowupMap p ∈ V.1 ∧
        pullback.snd f I.blowupMap p ∈ I.blowupMap ⁻¹ᵁ U.1 := by
  have hrange : Set.range (I.blowupι U) = (I.blowupMap ⁻¹ᵁ U.1 : Set ↥I.blowup) := by
    rw [I.blowupMap_preimage U]
    rfl
  have hrangeV : Set.range V.2.fromSpec = (V.1 : Set Y) := V.2.range_fromSpec
  have hR : Set.range (pullbackChart I f U V hVU) =
      pullback.fst f I.blowupMap ⁻¹' Set.range V.2.fromSpec ∩
        pullback.snd f I.blowupMap ⁻¹' Set.range (I.blowupι U) :=
    Scheme.Pullback.range_map _ _ f I.blowupMap V.2.fromSpec (I.blowupι U) U.2.fromSpec
      (specMap_ofHom_appLE_fromSpec f U V hVU) (I.blowupι_comp_blowupMap U).symm
  rw [hrangeV, hrange] at hR
  rw [Scheme.Hom.mem_opensRange, ← Set.mem_range, hR]
  exact Iff.rfl

/-- **The chart of the blow-up of the pulled-back ideal over `(U, V)`**: the blow-up chart of
`Bl_{I·O_Y}(Y)` at `V`, followed by the canonical morphism to `Y ×_X Bl_I(X)`, is the affine
base-change morphism of blow-ups followed by the chart of the fibre product at `(U, V)`. -/
lemma blowupι_comp_pullbackLift (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).blowupι V ≫ pullback.lift (I.comap f).blowupMap ρ hρ =
      pullback.lift (AffineBlowup.toSpec ((I.comap f).ideal V))
          (AffineBlowup.hom (f.appLE U.1 V.1 hVU).hom (I.ideal_comap_appLE f U V hVU).symm)
          (AffineBlowup.hom_toSpec _ (I.ideal_comap_appLE f U V hVU).symm).symm ≫
        pullbackChart I f U V hVU := by
  refine pullback.hom_ext ?_ ?_
  · unfold pullbackChart
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact (I.comap f).blowupι_comp_blowupMap V
  · unfold pullbackChart
    simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    exact I.blowupι_comp_of_le_preimage f hρ U V hVU

/-- The preimage of the chart of the fibre product at `(U, V)` under the canonical morphism
`Bl_{I·O_Y}(Y) ⟶ Y ×_X Bl_I(X)` is the blow-up chart of `Bl_{I·O_Y}(Y)` at `V`. -/
lemma preimage_opensRange_pullbackChart (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    pullback.lift (I.comap f).blowupMap ρ hρ ⁻¹ᵁ
      (pullbackChart I f U V hVU).opensRange = ((I.comap f).blowupι V).opensRange := by
  have hfst (z : ↥(I.comap f).blowup) :
      pullback.fst f I.blowupMap (pullback.lift (I.comap f).blowupMap ρ hρ z) =
        (I.comap f).blowupMap z := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  have hsnd (z : ↥(I.comap f).blowup) :
      pullback.snd f I.blowupMap (pullback.lift (I.comap f).blowupMap ρ hρ z) = ρ z := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rw [← (I.comap f).blowupMap_preimage V]
  refine TopologicalSpace.Opens.ext (Set.ext fun z ↦ ?_)
  simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage,
    mem_opensRange_pullbackChart I f U V hVU, hfst, hsnd]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, ← hρ, Scheme.Hom.comp_apply]
  exact hVU h

/-- **The chart-local form of the theorem.** Over the chart of `Y ×_X Bl_I(X)` at `(U, V)`,
the canonical morphism restricts to the affine base-change morphism of blow-ups, which is a
closed immersion by `AlgebraicGeometry.AffineBlowup.isClosedImmersion_pullbackLift`. -/
private lemma isClosedImmersion_pullbackLift_restrict (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    IsClosedImmersion (pullback.lift (I.comap f).blowupMap ρ hρ ∣_
      (pullbackChart I f U V hVU).opensRange) :=
  (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictArrowIso _ _ (I.blowupι_comp_pullbackLift f hρ U V hVU)
      (I.preimage_opensRange_pullbackChart f hρ U V hVU))).mpr
    (AffineBlowup.isClosedImmersion_pullbackLift _ (I.ideal_comap_appLE f U V hVU).symm)

/-- **The blow-up of a pulled-back ideal is a closed subscheme of the base-changed
blow-up** (Stacks Project Tag 080E, closed-immersion half; blueprint:
`thm:nagata-strict-transform-is-blowup`): for `f : Y ⟶ X`, an ideal sheaf `I` on `X`
and a lift `ρ` of `(I.comap f).blowupMap ≫ f` along `I.blowupMap` — provided by the
universal property of the blow-up, since the pullback of `I` to the blow-up of
`I.comap f` is the invertible exceptional ideal — the induced morphism
`Bl_{I·O_Y}(Y) ⟶ Y ×_X Bl_I(X)` is a closed immersion. -/
theorem isClosedImmersion_pullbackLift_blowup_comap (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap) :
    IsClosedImmersion (pullback.lift (I.comap f).blowupMap ρ hρ) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @IsClosedImmersion) fun p ↦ ?_
  obtain ⟨U, V, hVU, hpV⟩ := exists_affineOpens_le_preimage f (pullback.fst f I.blowupMap p)
  refine ⟨(pullbackChart I f U V hVU).opensRange, ?_,
    isClosedImmersion_pullbackLift_restrict I f hρ U V hVU⟩
  refine (mem_opensRange_pullbackChart I f U V hVU p).mpr ⟨hpV, ?_⟩
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← pullback.condition,
    Scheme.Hom.comp_apply]
  exact hVU hpV

end AlgebraicGeometry.Scheme.IdealSheafData
