/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Ordinary restricted scalar extension as tensor

Source: Stacks Project, Modules on Sites, Tag 05V4, and the scalar
extension-restriction argument in `lem-coef-integral-hom-reduction.proof.md`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe a b r

open CategoryTheory MonoidalCategory

namespace SheafOfModules
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)

set_option hygiene false in
local notation "A" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation "B" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
set_option hygiene false in
local notation "U" => SheafOfModules.restrictScalars
  ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Tensor cancellation at the quotient unit identifies restricted scalar extension.
Source: Stacks Tag 07A4. The cancellation comparison is natural in both variables;
take its first variable to be the quotient unit and compose its left unitor.
The sheaf braiding puts the fixed coefficient in the second variable.
(blueprint: lem-sf-ordinary-restriction-extension-tensor-comparison). -/
theorem restrictionExtensionTensorComparisonIndependentCoefficients (F : A ⥤ B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm) :
    Nonempty (F ⋙ U ≅ (curriedTensor A).flip.obj
      ((U).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))) := by
  classical
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let I : B := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  let c (M : A) := (U).mapIso (λ_ (SheafOfModules.changeOfRings φ M)).symm ≪≫ e I M
  have hc {M N : A} (f : M ⟶ N) :
      (U).map (SheafOfModules.changeOfRingsHom φ M f) ≫ (c N).hom =
        (c M).hom ≫ (tensorLeft ((U).obj I)).map f := by
    dsimp only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← (U).map_comp, leftUnitor_inv_naturality,
      (U).map_comp, Category.assoc]
    have hn := he (𝟙 I) f
    rw [(U).map_id] at hn
    change (U).map (λ_ (SheafOfModules.changeOfRings φ M)).inv ≫
      (U).map (I ◁ SheafOfModules.changeOfRingsHom φ M f) ≫ (e I N).hom = _
    simpa only [tensorLeft, curriedTensor_obj_map, id_tensorHom, Category.assoc] using
      congrArg (fun k ↦ (U).map (λ_ (SheafOfModules.changeOfRings φ M)).inv ≫ k) hn
  let c' : F ⋙ U ≅ tensorLeft ((U).obj I) :=
    NatIso.ofComponents (fun M ↦ (U).mapIso (eqToIso (h M)) ≪≫ c M) (by
      intro M N f
      dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
      rw [← Category.assoc, ← (U).map_comp, hm]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [(U).map_comp, Category.assoc, hc])
  exact ⟨c' ≪≫ BraidedCategory.tensorLeftIsoTensorRight ((U).obj I)⟩

end SheafOfModules
