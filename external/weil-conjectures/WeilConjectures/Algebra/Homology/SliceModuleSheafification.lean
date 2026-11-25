/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Abelian

/-! # Module sheafification under continuous cocontinuous restriction

Source: Stacks Project, Tags 03CY, 03DH and 04IX.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u
open CategoryTheory
namespace SheafOfModules

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (R : Sheaf K RingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => (F.sheafPushforwardContinuous RingCat.{u} J K).obj R

/-- Restriction of module presheaves along the given site functor.
Source: Stacks 04IX (auxiliary; not a blueprint node). -/
abbrev slicePresheafRestriction : PresheafOfModules.{u} R.obj ⥤ PresheafOfModules.{u} (A).obj :=
  PresheafOfModules.pushforward₀.{u} F R.obj

/-- The corresponding restriction of sheaf modules.
Source: Stacks 04IX (auxiliary; not a blueprint node). -/
abbrev sliceModuleRestriction : SheafOfModules.{u} R ⥤ SheafOfModules.{u} A :=
  pushforward.{u} (F := F) (𝟙 A)

/-- Extend the restricted global sheafification unit by the local sheafification adjunction.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def sliceSheafificationComparison :
    slicePresheafRestriction (J := J) F R ⋙ PresheafOfModules.sheafification (𝟙 (A).obj) ⟶
      PresheafOfModules.sheafification (𝟙 R.obj) ⋙ sliceModuleRestriction (J := J) F R := by
  let P := slicePresheafRestriction (J := J) F R
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let T := PresheafOfModules.sheafification (𝟙 (A).obj)
  let V := sliceModuleRestriction (J := J) F R
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let b := PresheafOfModules.sheafificationAdjunction (𝟙 (A).obj)
  exact
    { app M := (b.homEquiv _ _).symm (P.map (a.unit.app M))
      naturality {M N} f := by
        change T.map (P.map f) ≫
          (b.homEquiv (P.obj N) (V.obj (S.obj N))).symm (P.map (a.unit.app N)) =
            (b.homEquiv (P.obj M) (V.obj (S.obj M))).symm (P.map (a.unit.app M)) ≫
              V.map (S.map f)
        erw [← b.homEquiv_naturality_left_symm, ← b.homEquiv_naturality_right_symm]
        congr 1
        change P.map f ≫ P.map (a.unit.app N) =
          P.map (a.unit.app M) ≫
            P.map ((forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map (S.map f))
        rw [← P.map_comp, ← P.map_comp]
        exact congrArg P.map (a.unit.naturality f) }

/-- The comparison is an isomorphism for continuous cocontinuous restriction.
Source: Stacks 03CY and 03DH
(auxiliary; not a blueprint node).
Proof: The sheafification adjunction identifies the comparison composed with the
local unit with the restricted global unit. The global unit is locally bijective,
and cocontinuity preserves local injectivity and local surjectivity under restriction.
Cancel the locally bijective local unit to see that the comparison is locally
bijective. Its source and target are sheaves, so it is an isomorphism. -/
theorem sliceSheafificationComparison_isIso :
    IsIso (sliceSheafificationComparison (J := J) F R) := by
  let P := slicePresheafRestriction (J := J) F R
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let V := sliceModuleRestriction (J := J) F R
  let b := PresheafOfModules.sheafificationAdjunction (𝟙 (A).obj)
  let t := sliceSheafificationComparison (J := J) F R
  have ht (M : PresheafOfModules.{u} R.obj) :
      CategoryTheory.toSheafify J (P.obj M).presheaf ≫
          (PresheafOfModules.toPresheaf (A).obj).map (t.app M).val =
        Functor.whiskerLeft F.op (CategoryTheory.toSheafify K M.presheaf) := by
    have h := (b.homEquiv (P.obj M) (V.obj (S.obj M))).apply_symm_apply
      (show P.obj M ⟶ (forget A ⋙ PresheafOfModules.restrictScalars (𝟙 (A).obj)).obj
        (V.obj (S.obj M)) from P.map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M))
    exact congrArg ((PresheafOfModules.toPresheaf (A).obj).map) h
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf A)]
  apply (Sheaf.isLocallyBijective_iff_isIso (J := J)
    ((SheafOfModules.toSheaf A).map (t.app M))).mp
  have h₁ : Presheaf.IsLocallyInjective J
      (Functor.whiskerLeft F.op (CategoryTheory.toSheafify K M.presheaf)) :=
    Presheaf.isLocallyInjective_whisker J K F _
  have h₂ : Presheaf.IsLocallySurjective J
      (Functor.whiskerLeft F.op (CategoryTheory.toSheafify K M.presheaf)) :=
    Presheaf.isLocallySurjective_whisker J K F _
  have : Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (P.obj M).presheaf) :=
    (J.W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (P.obj M).presheaf) :=
    (J.W_toSheafify _).isLocallySurjective
  rw [← ht M] at h₁ h₂
  exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp h₁,
    (Presheaf.comp_isLocallySurjective_iff _ _ _).mp h₂⟩

/-- The canonical sheafification/restriction isomorphism, with its fixed orientation.
Source: Stacks 03CY, 03DH and 04IX
(auxiliary; not a blueprint node). -/
def sliceSheafificationIso :
    PresheafOfModules.sheafification (𝟙 R.obj) ⋙ sliceModuleRestriction (J := J) F R ≅
      slicePresheafRestriction (J := J) F R ⋙ PresheafOfModules.sheafification (𝟙 (A).obj) :=
  haveI := sliceSheafificationComparison_isIso (J := J) F R
  (asIso (sliceSheafificationComparison (J := J) F R)).symm

end SheafOfModules
