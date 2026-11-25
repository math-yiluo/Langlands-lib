/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Normalized constant sheaf units and site comparisons -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J E] [HasWeakSheafify K E]
  (F : C ⥤ D) [F.IsContinuous J K]
  (L : Sheaf J E ⥤ Sheaf K E)
  (a : L ⊣ F.sheafPushforwardContinuous E J K)
  {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))

private def constantPullIso : constantSheaf J E ⋙ L ≅ constantSheaf K E :=
  ((constantSheafAdj J E hT).comp a).leftAdjointUniq (constantSheafAdj K E hFT)

private lemma constantPullIso_unit (N : E) :
    toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫
      (a.homEquiv _ _ ((constantPullIso J K F L a hT hFT).hom.app N)).hom =
    whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N)) := by
  let e := constantPullIso J K F L a hT hFT
  let g := a.homEquiv _ _ (e.hom.app N)
  let u := toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫ g.hom
  let v := whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N))
  have ht : u.app (op T) = v.app (op T) := by
    have h := ((constantSheafAdj J E hT).comp a).homEquiv_leftAdjointUniq_hom_app
      (constantSheafAdj K E hFT) N
    rw [Adjunction.comp_homEquiv] at h
    change (constantSheafAdj J E hT).homEquiv N _
      (a.homEquiv _ _ (e.hom.app N)) = (constantSheafAdj K E hFT).unit.app N at h
    rw [constantSheafAdj_homEquiv_apply] at h
    have hu : (constantSheafAdj K E hFT).unit.app N = v.app (op T) := by
      rw [← Adjunction.homEquiv_id, constantSheafAdj_homEquiv_apply]
      exact Category.comp_id _
    exact h.trans hu
  apply NatTrans.ext
  funext Z
  let i : op T ⟶ Z := (hT.from Z.unop).op
  have hu := u.naturality i
  have hv := v.naturality i
  change 𝟙 N ≫ u.app Z = u.app (op T) ≫ _ at hu
  change 𝟙 N ≫ v.app Z = v.app (op T) ≫ _ at hv
  rw [Category.id_comp] at hu hv
  exact hu.trans ((congrArg (fun k ↦ k ≫ _) ht).trans hv.symm)

end

section
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
  (J : GrothendieckTopology C) {B D : Type (t + 1)} [CommRing B] [CommRing D]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} D)] (q : B →+* D)
  [J.PreservesSheafification (ModuleCat.restrictScalars.{t + 1} q)]
private abbrev constantCoefficientRestriction := ModuleCat.restrictScalars.{t + 1} q

omit [EssentiallySmall.{t + 1} C] in
private lemma constantCompose_hom_unit (N : ModuleCat.{t + 1} D) :
    whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N)) (constantCoefficientRestriction q) ≫
        ((constantCommuteCompose J (constantCoefficientRestriction q)).hom.app N).hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj ((constantCoefficientRestriction q).obj N)) := by
  rw [constantCommuteCompose_hom_app_hom]
  change whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N))
      (constantCoefficientRestriction q) ≫
    ((sheafifyComposeIso J (constantCoefficientRestriction q) ((Functor.const Cᵒᵖ).obj N)).inv ≫
      sheafifyMap J (𝟙 _)) = _
  erw [sheafComposeIso_inv_fac_assoc, sheafifyMap_id, Category.comp_id]
  rfl

omit [EssentiallySmall.{t + 1} C] in
private lemma constantCompose_inv_unit (N : ModuleCat.{t + 1} D) :
    toSheafify J ((Functor.const Cᵒᵖ).obj ((constantCoefficientRestriction q).obj N)) ≫
        ((constantCommuteCompose J (constantCoefficientRestriction q)).inv.app N).hom =
      whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N))
      (constantCoefficientRestriction q) := by
  rw [← constantCompose_hom_unit J q N, Category.assoc]
  have h := congrArg (fun f ↦ f.hom)
    ((constantCommuteCompose J (constantCoefficientRestriction q)).hom_inv_id_app N)
  change ((constantCommuteCompose J (constantCoefficientRestriction q)).hom.app N).hom ≫
    ((constantCommuteCompose J (constantCoefficientRestriction q)).inv.app N).hom = 𝟙 _ at h
  erw [h, Category.comp_id]

end

section
variable {C D : Type (t + 1)} [Category.{t} C] [Category.{t} D]
  [EssentiallySmall.{t + 1} C] [EssentiallySmall.{t + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {B E : Type (t + 1)} [CommRing B] [CommRing E]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} E)]
  [HasWeakSheafify K (ModuleCat.{t + 1} B)]
  [HasWeakSheafify K (ModuleCat.{t + 1} E)]
  (F : C ⥤ D) [F.IsContinuous J K] {T : C}
  (hT : IsTerminal T) (hFT : IsTerminal (F.obj T)) (q : B →+* E)

private lemma constantPull_coefficient (N : ModuleCat.{t + 1} E) :
    let PB := Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{t + 1} B) J K
    let PE := Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{t + 1} E) J K
    let aB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
      (ModuleCat.{t + 1} B) J K
    let aE := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
      (ModuleCat.{t + 1} E) J K
    let eB := constantPullIso J K F PB aB hT hFT
    let eE := constantPullIso J K F PE aE hT hFT
    PB.map ((constantCommuteCompose J (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (normalizationPullbackMate J F K q).app
        ((constantSheaf J (ModuleCat.{t + 1} E)).obj N) ≫
      (sheafCompose K (ModuleCat.restrictScalars.{t + 1} q)).map (eE.hom.app N) ≫
      (constantCommuteCompose K (ModuleCat.restrictScalars.{t + 1} q)).hom.app N =
    eB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) := by
  dsimp only
  let U := ModuleCat.restrictScalars.{t + 1} q
  let PJ := sheafCompose J U
  let PK := sheafCompose K U
  let PB := Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{t + 1} B) J K
  let PE := Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{t + 1} E) J K
  let aB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    (ModuleCat.{t + 1} B) J K
  let aE := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    (ModuleCat.{t + 1} E) J K
  let eB := constantPullIso J K F PB aB hT hFT
  let eE := constantPullIso J K F PE aE hT hFT
  let γJ := constantCommuteCompose J U
  let γK := constantCommuteCompose K U
  let Y := (constantSheaf J (ModuleCat.{t + 1} E)).obj N
  let β := (normalizationPullbackMate J F K q).app Y
  have hβ : aB.homEquiv _ _ β = PJ.map (aE.unit.app Y) := by
    have h := unit_mateEquiv_symm aE aB (TwoSquare.mk
      (F.sheafPushforwardContinuous (ModuleCat.{t + 1} E) J K) PK PJ
      (F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K) (𝟙 _)) Y
    change PJ.map (aE.unit.app Y) ≫ 𝟙 _ =
      aB.unit.app (PJ.obj Y) ≫
        (F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K).map β at h
    rw [Category.comp_id] at h
    exact h.symm
  apply (aB.homEquiv _ _).injective
  change aB.homEquiv _ _
      (PB.map (γJ.inv.app N) ≫ β ≫ PK.map (eE.hom.app N) ≫ γK.hom.app N) =
    aB.homEquiv _ _ (eB.hom.app (U.obj N))
  erw [aB.homEquiv_naturality_left, aB.homEquiv_naturality_right, hβ]
  erw [(F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K).map_comp]
  change γJ.inv.app N ≫ PJ.map (aE.unit.app Y) ≫
      PJ.map ((F.sheafPushforwardContinuous (ModuleCat.{t + 1} E) J K).map
        (eE.hom.app N)) ≫
      (F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K).map
        (γK.hom.app N) = _
  rw [← PJ.map_comp_assoc]
  change γJ.inv.app N ≫ PJ.map (aE.homEquiv _ _ (eE.hom.app N)) ≫
    (F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K).map (γK.hom.app N) = _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K).obj
      ((constantSheaf K (ModuleCat.{t + 1} B)).obj (U.obj N))).property
  change toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)) ≫
      (γJ.inv.app N).hom ≫
      whiskerRight (aE.homEquiv _ _ (eE.hom.app N)).hom U ≫
      whiskerLeft F.op (γK.hom.app N).hom =
    toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)) ≫
      (aB.homEquiv _ _ (eB.hom.app (U.obj N))).hom
  rw [← Category.assoc, ← Category.assoc, constantCompose_inv_unit J q N]
  erw [← Functor.whiskerRight_comp, constantPullIso_unit]
  change whiskerLeft F.op
      (whiskerRight (toSheafify K ((Functor.const Dᵒᵖ).obj N)) U) ≫
      whiskerLeft F.op (γK.hom.app N).hom = _
  erw [← Functor.whiskerLeft_comp, constantCompose_hom_unit K q N]
  exact (constantPullIso_unit J K F PB aB hT hFT (U.obj N)).symm

end

section
variable {C D : Type (t + 1)} [Category.{t} C] [Category.{t} D]
  [EssentiallySmall.{t + 1} C] [EssentiallySmall.{t + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {B E : Type (t + 1)} [CommRing B] [CommRing E]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} E)]
  [HasWeakSheafify K (ModuleCat.{t + 1} B)]
  [HasWeakSheafify K (ModuleCat.{t + 1} E)]
  (F : C ⥤ D) [F.IsContinuous J K] (q : B →+* E)
  (eB : constantSheaf K (ModuleCat.{t + 1} B) ⋙
      F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K ≅
    constantSheaf J (ModuleCat.{t + 1} B))
  (eE : constantSheaf K (ModuleCat.{t + 1} E) ⋙
      F.sheafPushforwardContinuous (ModuleCat.{t + 1} E) J K ≅
    constantSheaf J (ModuleCat.{t + 1} E))
  (hB : ∀ N, toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫
    (eB.inv.app N).hom = whiskerLeft F.op
      (toSheafify K ((Functor.const Dᵒᵖ).obj N)))
  (hE : ∀ N, whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N)) ≫
    (eE.hom.app N).hom = toSheafify J ((Functor.const Cᵒᵖ).obj N))

include hB hE in
private lemma constantPush_coefficient (N : ModuleCat.{t + 1} E) :
    (F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K).map
        ((constantCommuteCompose K (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (sheafCompose J (ModuleCat.restrictScalars.{t + 1} q)).map (eE.hom.app N) ≫
      (constantCommuteCompose J (ModuleCat.restrictScalars.{t + 1} q)).hom.app N =
    eB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) := by
  let U := ModuleCat.restrictScalars.{t + 1} q
  let γJ := constantCommuteCompose J U
  let γK := constantCommuteCompose K U
  apply (cancel_epi (eB.inv.app (U.obj N))).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((constantSheaf J (ModuleCat.{t + 1} B)).obj (U.obj N)).property
  have hi := congrArg (fun f ↦ f.hom) (eB.inv_hom_id_app (U.obj N))
  change toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)) ≫
      (eB.inv.app (U.obj N)).hom ≫
      whiskerLeft F.op (γK.inv.app N).hom ≫ whiskerRight (eE.hom.app N).hom U ≫
      (γJ.hom.app N).hom =
    toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)) ≫
      ((eB.inv.app (U.obj N)).hom ≫ (eB.hom.app (U.obj N)).hom)
  change (eB.inv.app (U.obj N)).hom ≫ (eB.hom.app (U.obj N)).hom = 𝟙 _ at hi
  erw [hi, Category.comp_id, ← Category.assoc, ← Category.assoc, ← Category.assoc, hB]
  erw [← Functor.whiskerLeft_comp, constantCompose_inv_unit K q N]
  change whiskerRight (whiskerLeft F.op
      (toSheafify K ((Functor.const Dᵒᵖ).obj N))) U ≫
      whiskerRight (eE.hom.app N).hom U ≫ (γJ.hom.app N).hom = _
  erw [← Functor.whiskerRight_comp_assoc, hE, constantCompose_hom_unit J q N]

end

section
variable {C D A : Type*} [Category C] [Category D] [Category A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (F : C ⥤ D) [F.IsContinuous J K]
  (e : constantSheaf K A ⋙ F.sheafPushforwardContinuous A J K ≅ constantSheaf J A)
  (h : ∀ N, toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫ (e.inv.app N).hom =
    whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N)))
include h in
private lemma constantPush_hom_unit (N : A) :
    whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N)) ≫ (e.hom.app N).hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj N) := by
  rw [← h, Category.assoc]
  have hi := congrArg (fun f ↦ f.hom) (e.inv_hom_id_app N)
  change (e.inv.app N).hom ≫ (e.hom.app N).hom = 𝟙 _ at hi
  erw [hi, Category.comp_id]
end

section
variable {C D H : Type (t + 1)} [Category.{t} C] [Category.{t} D] [Category.{t} H]
  [EssentiallySmall.{t + 1} C] [EssentiallySmall.{t + 1} D] [EssentiallySmall.{t + 1} H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology H)
  {B E : Type (t + 1)} [CommRing B] [CommRing E]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} E)]
  [HasWeakSheafify K (ModuleCat.{t + 1} B)]
  [HasWeakSheafify K (ModuleCat.{t + 1} E)]
  [HasWeakSheafify L (ModuleCat.{t + 1} B)]
  [HasWeakSheafify L (ModuleCat.{t + 1} E)]
  (q : B →+* E)
  (FB : Sheaf J (ModuleCat.{t + 1} B) ⥤ Sheaf K (ModuleCat.{t + 1} B))
  (FE : Sheaf J (ModuleCat.{t + 1} E) ⥤ Sheaf K (ModuleCat.{t + 1} E))
  (GB : Sheaf K (ModuleCat.{t + 1} B) ⥤ Sheaf L (ModuleCat.{t + 1} B))
  (GE : Sheaf K (ModuleCat.{t + 1} E) ⥤ Sheaf L (ModuleCat.{t + 1} E))
  (βF : sheafCompose J (ModuleCat.restrictScalars.{t + 1} q) ⋙ FB ⟶
    FE ⋙ sheafCompose K (ModuleCat.restrictScalars.{t + 1} q))
  (βG : sheafCompose K (ModuleCat.restrictScalars.{t + 1} q) ⋙ GB ⟶
    GE ⋙ sheafCompose L (ModuleCat.restrictScalars.{t + 1} q))
  (eFB : constantSheaf J (ModuleCat.{t + 1} B) ⋙ FB ≅ constantSheaf K (ModuleCat.{t + 1} B))
  (eFE : constantSheaf J (ModuleCat.{t + 1} E) ⋙ FE ≅ constantSheaf K (ModuleCat.{t + 1} E))
  (eGB : constantSheaf K (ModuleCat.{t + 1} B) ⋙ GB ≅ constantSheaf L (ModuleCat.{t + 1} B))
  (eGE : constantSheaf K (ModuleCat.{t + 1} E) ⋙ GE ≅ constantSheaf L (ModuleCat.{t + 1} E))
  (hF : ∀ N, FB.map ((constantCommuteCompose J
      (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
    βF.app ((constantSheaf J (ModuleCat.{t + 1} E)).obj N) ≫
    (sheafCompose K (ModuleCat.restrictScalars.{t + 1} q)).map (eFE.hom.app N) =
      eFB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) ≫
        (constantCommuteCompose K (ModuleCat.restrictScalars.{t + 1} q)).inv.app N)
  (hG : ∀ N, GB.map ((constantCommuteCompose K
      (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
    βG.app ((constantSheaf K (ModuleCat.{t + 1} E)).obj N) ≫
    (sheafCompose L (ModuleCat.restrictScalars.{t + 1} q)).map (eGE.hom.app N) =
      eGB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) ≫
        (constantCommuteCompose L (ModuleCat.restrictScalars.{t + 1} q)).inv.app N)

include hF hG in
private lemma constantCoefficient_comp (N : ModuleCat.{t + 1} E) :
    GB.map (FB.map ((constantCommuteCompose J
        (ModuleCat.restrictScalars.{t + 1} q)).inv.app N)) ≫
      GB.map (βF.app ((constantSheaf J (ModuleCat.{t + 1} E)).obj N)) ≫
      βG.app (FE.obj ((constantSheaf J (ModuleCat.{t + 1} E)).obj N)) ≫
      (sheafCompose L (ModuleCat.restrictScalars.{t + 1} q)).map
        (GE.map (eFE.hom.app N) ≫ eGE.hom.app N) =
    GB.map (eFB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N)) ≫
      eGB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) ≫
      (constantCommuteCompose L (ModuleCat.restrictScalars.{t + 1} q)).inv.app N := by
  rw [Functor.map_comp]
  erw [← βG.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← GB.map_comp_assoc, ← GB.map_comp_assoc]
  simp only [Category.assoc]
  rw [hF, GB.map_comp, Category.assoc, hG]

end

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
