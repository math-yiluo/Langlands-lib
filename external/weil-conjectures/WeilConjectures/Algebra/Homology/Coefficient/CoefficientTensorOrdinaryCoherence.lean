/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension

/-!
# Normalized ordinary quotient tensor coherence

Source: Zheng, Construction 4.1, p. 21; Stacks Tags 03D7 and 03EK.
(blueprint: lem-pur-coefficient-tensor-ordinary-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def coefficientRingQuotients : ℕᵒᵖ ⥤ CommRingCat.{w} where
  obj n := CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n.unop + 1))
  map f := CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1)))
  map_id n := by
    apply CommRingCat.hom_ext
    exact Ideal.Quotient.factor_eq
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact (Ideal.Quotient.factor_comp
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))).symm

private def coefficientRings : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w} where
  obj n := coefficientQuotientSheaf (J := J) O ell n.unop
  map f := coefficientQuotientMap (J := J) O ell (leOfHom f.unop)
  map_id n := (coefficientRingQuotients (O := O) (ell := ell) ⋙
    constantSheaf J CommRingCat.{w}).map_id n
  map_comp f g := (coefficientRingQuotients (O := O) (ell := ell) ⋙
    constantSheaf J CommRingCat.{w}).map_comp f g

private def coefficientScalarIso
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ) :
    D.model.E ≅ siteCoefficientTensor φ :=
  NatIso.ofComponents (fun F ↦ eqToIso (D.model.obj_eq F)) (by
    intro F G f
    change D.model.E.map f ≫ eqToHom (D.model.obj_eq G) =
      eqToHom (D.model.obj_eq F) ≫ changeOfRingsHom φ F f
    rw [D.model.map_eq]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

private theorem coefficientModelUnit
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ)
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (x : F.val.obj U) :
    ((coefficientScalarIso φ D).hom.app F).val.app U
      ((D.ordinaryAdj.unit.app F).val.app U x) =
      ((siteCoefficientTensorAdj φ).unit.app F).val.app U x := by
  let z := (toSheafify J (changeOfRingsPresheaf φ F).presheaf).app U
    (((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (F.val.obj U)) x)
  have hn := (siteCoefficientTensorAdj_exists φ).exists.choose_spec
    F ((siteCoefficientTensor φ).obj F) (𝟙 _) U x
  rw [Adjunction.homEquiv_id] at hn
  change ((siteCoefficientTensorAdj φ).unit.app F).val.app U x = z at hn
  rw [D.unit_normalized, hn]
  change (eqToHom (D.model.obj_eq F)).val.app U
    (1 • (eqToHom (D.model.obj_eq F).symm).val.app U z) = z
  simp only [one_smul]
  change ((eqToHom (D.model.obj_eq F).symm ≫
    eqToHom (D.model.obj_eq F)).val.app U) z = z
  simp only [eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]

omit [HasWeakSheafify J CommRingCat.{w}] in
private theorem coefficientModelUnit_naturality
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ)
    {F G : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)}
    (f : F ⟶ G) (U : Cᵒᵖ) (x : F.val.obj U) :
    (D.model.E.map f).val.app U ((D.ordinaryAdj.unit.app F).val.app U x) =
      (D.ordinaryAdj.unit.app G).val.app U (f.val.app U x) := by
  have h := D.ordinaryAdj.unit.naturality f
  exact congrArg (fun g : F ⟶ (restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj
      (D.model.E.obj G) ↦ (g.val.app U) x) h.symm

private def modelUnit
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ)
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :
    (toSheaf _).obj F ⟶ (toSheaf _).obj (D.model.E.obj F) :=
  (toSheaf _).map (D.ordinaryAdj.unit.app F) ≫
    (siteScalarUnderlyingIso φ).hom.app (D.model.E.obj F)

private theorem modelUnit_hom
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ)
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :
    modelUnit φ D F ≫ (toSheaf _).map ((coefficientScalarIso φ D).hom.app F) =
      siteTensorUnitUnderlying φ F := by
  ext U x
  exact coefficientModelUnit φ D F U x

private theorem modelUnit_inv
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ)
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :
    siteTensorUnitUnderlying φ F ≫ (toSheaf _).map ((coefficientScalarIso φ D).inv.app F) =
      modelUnit φ D F := by
  apply (cancel_mono ((toSheaf _).map ((coefficientScalarIso φ D).hom.app F))).1
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, modelUnit_hom]

omit [HasWeakSheafify J CommRingCat.{w}] in
private theorem modelUnit_naturality
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (D : SystemScalarModel φ)
    {F G : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)} (f : F ⟶ G) :
    modelUnit φ D F ≫ (toSheaf _).map (D.model.E.map f) =
      (toSheaf _).map f ≫ modelUnit φ D G := by
  ext U x
  exact coefficientModelUnit_naturality φ D f U x

private abbrev ordinaryTensor (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    {m n : ℕ} (h : n ≤ m) := siteCoefficientTensor (B.map (homOfLE h).op)

attribute [local irreducible] siteCoefficientTensor siteCoefficientTensorAdj coefficientScalarIso

private theorem ordinaryTensorCoherence
    (t : SystemLevelLeftExtensionTheory (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) :
    ∃ unit : ∀ n, ordinaryTensor B (Nat.le_refl n) ≅ 𝟭 _,
      (∀ n F, siteTensorUnitUnderlying (B.map (homOfLE (Nat.le_refl n)).op) F ≫
        (toSheaf _).map ((unit n).hom.app F) = 𝟙 _) ∧
      ∃ assoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
        ordinaryTensor B h₁ ⋙ ordinaryTensor B h₂ ≅ ordinaryTensor B (h₂.trans h₁),
      ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) F,
        siteTensorUnitUnderlying (B.map (homOfLE h₁).op) F ≫
          siteTensorUnitUnderlying (B.map (homOfLE h₂).op) ((ordinaryTensor B h₁).obj F) ≫
          (toSheaf _).map ((assoc h₁ h₂).hom.app F) =
          siteTensorUnitUnderlying (B.map (homOfLE (h₂.trans h₁)).op) F := by
  let hi {m n : ℕ} (h : n ≤ m) :
      systemTensor t.scalar B h ≅ ordinaryTensor B h := coefficientScalarIso _ (t.scalar _)
  let unit n := (hi (Nat.le_refl n)).symm ≪≫ t.tensor.ordinaryUnit B n
  let assoc {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m) :=
    CategoryTheory.Functor.isoWhiskerLeft (ordinaryTensor B h₁) (hi h₂).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight (hi h₁).symm
        (systemTensor t.scalar B h₂) ≪≫
      t.tensor.ordinaryAssoc B h₂ h₁ ≪≫ hi (h₂.trans h₁)
  refine ⟨unit, ?_, assoc, ?_⟩
  · intro n F
    change siteTensorUnitUnderlying _ F ≫
      (toSheaf _).map ((hi (Nat.le_refl n)).inv.app F ≫
        (t.tensor.ordinaryUnit B n).hom.app F) = _
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, modelUnit_inv]
    ext U x
    have h := t.tensor.unit_normalized B n F U 1 x
    rw [← (t.scalar _).unit_normalized] at h
    exact h.trans (one_smul _ _)
  · intro l m n h₁ h₂ F
    let e₁ := hi h₁
    let e₂ := hi h₂
    let e₃ := hi (h₂.trans h₁)
    let D₁ := t.scalar (B.map (homOfLE h₁).op)
    let D₂ := t.scalar (B.map (homOfLE h₂).op)
    let D₃ := t.scalar (B.map (homOfLE (h₂.trans h₁)).op)
    let a := (t.tensor.ordinaryAssoc B h₂ h₁).hom.app F
    have ha : modelUnit _ D₁ F ≫ modelUnit _ D₂ (D₁.model.E.obj F) ≫
        (toSheaf _).map a = modelUnit _ D₃ F := by
      ext U x
      have h := t.tensor.assoc_normalized B h₂ h₁ F U 1 1 x
      simp only [map_one, one_mul] at h
      rw [← D₂.unit_normalized, ← D₁.unit_normalized, ← D₃.unit_normalized] at h
      exact h
    change siteTensorUnitUnderlying _ F ≫ siteTensorUnitUnderlying _
      ((ordinaryTensor B h₁).obj F) ≫ (toSheaf _).map
        (e₂.inv.app _ ≫ D₂.model.E.map (e₁.inv.app F) ≫ a ≫ e₃.hom.app F) = _
    simp only [CategoryTheory.Functor.map_comp]
    calc
      _ = siteTensorUnitUnderlying _ F ≫
          (siteTensorUnitUnderlying _ ((ordinaryTensor B h₁).obj F) ≫
            (toSheaf _).map (e₂.inv.app _)) ≫
          (toSheaf _).map (D₂.model.E.map (e₁.inv.app F)) ≫
          (toSheaf _).map a ≫ (toSheaf _).map (e₃.hom.app F) := by
        simp only [Category.assoc]
      _ = siteTensorUnitUnderlying _ F ≫ modelUnit _ D₂ ((ordinaryTensor B h₁).obj F) ≫
          (toSheaf _).map (D₂.model.E.map (e₁.inv.app F)) ≫
          (toSheaf _).map a ≫ (toSheaf _).map (e₃.hom.app F) := by rw [modelUnit_inv]
      _ = siteTensorUnitUnderlying _ F ≫ (toSheaf _).map (e₁.inv.app F) ≫
          modelUnit _ D₂ (D₁.model.E.obj F) ≫
          (toSheaf _).map a ≫ (toSheaf _).map (e₃.hom.app F) := by
        rw [← Category.assoc (modelUnit _ D₂ _) ((toSheaf _).map (D₂.model.E.map _)),
          modelUnit_naturality]
        simp only [Category.assoc]
        rfl
      _ = modelUnit _ D₁ F ≫ modelUnit _ D₂ (D₁.model.E.obj F) ≫
          (toSheaf _).map a ≫ (toSheaf _).map (e₃.hom.app F) := by
        rw [← Category.assoc (siteTensorUnitUnderlying _ F), modelUnit_inv]
      _ = (modelUnit _ D₁ F ≫ modelUnit _ D₂ (D₁.model.E.obj F) ≫
          (toSheaf _).map a) ≫ (toSheaf _).map (e₃.hom.app F) := by
        simp only [Category.assoc]
      _ = modelUnit _ D₃ F ≫ (toSheaf _).map (e₃.hom.app F) := by rw [ha]
      _ = _ := modelUnit_hom _ D₃ F

/-- The specified quotient tensors have the unit and associator determined by their
canonical scalar-extension units.
Source: Stacks Tags 03D7 and 03EK; Zheng, Construction 4.1
(blueprint: lem-pur-coefficient-tensor-ordinary-coherence).
Proof: use the ordinary scalar coherence of the strict-system theory on the diagram
of constant quotient rings. Its scalar models equal the prescribed tensor functors by
their object and map formulas. Transport its unit and associator along these equalities.
The normalized scalar Hom formulas identify the model's scalar-extension units with the
specified units. The unit evaluates to x on 1 tensor x, and the associator sends
1 tensor (1 tensor x) to 1 tensor x. Equality on sections gives the asserted equations
of underlying additive-sheaf maps. -/
theorem coefficientTensorOrdinaryCoherence :
    ∃ unit : ∀ n, coefficientTensor (J := J) (O := O) (ell := ell) (Nat.le_refl n) ≅ 𝟭 _,
      CoefficientTensorUnitNormalized unit ∧
      ∃ assoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
        coefficientTensor (J := J) (O := O) (ell := ell) h₁ ⋙
          coefficientTensor (J := J) (O := O) (ell := ell) h₂ ≅
            coefficientTensor (J := J) (O := O) (ell := ell) (h₂.trans h₁),
        CoefficientTensorAssocNormalized assoc := by
  classical
  obtain ⟨unit, hu, assoc, ha⟩ := ordinaryTensorCoherence
    (systemLevelLeftExtensionTheory (J := J)).some
    (coefficientRings (J := J) (O := O) (ell := ell))
  exact ⟨unit, hu, (fun {_ _ _} h₁ h₂ ↦ assoc h₁ h₂), ha⟩

end SheafOfModules
