/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
/-!
# Normalized composition of derived coefficient extensions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YY and 07A6
(auxiliary; not a blueprint node).

The scalar-first tensor convention of `changeOfRings` writes the paper's
`(x ⊗ s) ⊗ t` as `t ⊗ (s ⊗ x)`. All the comparison maps below refer to the
existing sheafified extension, its universal left derived pair, and its
localization counit. The auxiliary presentations only bundle these interfaces.
-/

@[expose] public section

set_option autoImplicit false

universe u v r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.SuccessiveDerivedQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

variable [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem presentation_exists {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    Nonempty (Presentation a) := by
  obtain ⟨E, hobj, hmap, hadd, _, _, LF, eps, hLF, _, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients (J := J) a
  exact ⟨{
    ordinary := E, obj_eq := hobj, map_eq := hmap, additive := hadd,
    derived := LF, counit := eps, universal := hLF
  }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem restriction_exact {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (restriction a) ∧ PreservesFiniteColimits (restriction a) := by
  obtain ⟨hl, hc, _⟩ := sheafRingDerivedCoefficientAdjunction (J := J) a
  exact ⟨hl, hc⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private local instance restriction_limits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (restriction a) := (restriction_exact a).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private local instance restriction_colimits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteColimits (restriction a) := (restriction_exact a).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private structure AdjData {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation a) where
  ordinary : p.ordinary ⊣ restriction a
  ordinary_unit : ∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U),
    (ordinary.unit.app M).val.app U x = sectionTensor p M U 1 x
  derived : p.derived ⊣ (restriction a).mapDerivedCategory
  computed : ∀ (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso (p.counit.app ((HomotopyCategory.quotient _ _).obj P))
  unit_normalization : ∀ (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    derived.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (restriction a).mapDerivedCategory.map
        (p.counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (restriction a).mapDerivedCategoryFactorsh.hom.app
        ((p.ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      ((ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  hom_comparison : ∀ (H : HomotopyCategory (Modules R) (ComplexShape.up ℤ))
    (K : HomotopyCategory (Modules S) (ComplexShape.up ℤ))
    (f : (p.ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj H ⟶ K),
    derived.homEquiv _ _ (p.counit.app H ≫ DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map
        ((ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv H K f) ≫
      (restriction a).mapDerivedCategoryFactorsh.inv.app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem adjData_exists {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation a) : Nonempty (AdjData p) := by
  obtain ⟨_, _, h⟩ := sheafRingDerivedCoefficientAdjunction (J := J) a
  obtain ⟨A, hA, hD⟩ := h p.ordinary p.obj_eq p.map_eq
  obtain ⟨D₀, hD₀⟩ := hD p.derived p.counit p.universal
  obtain ⟨D, hd⟩ := sheafRingDerivedHomComparison a p.ordinary p.obj_eq p.map_eq A
    p.derived p.counit p.universal
  refine ⟨{
    ordinary := A
    ordinary_unit := ?_
    derived := D
    computed := fun P hP hf ↦ (hD₀ P hP hf).1
    hom_comparison := hd
    unit_normalization := ?_
  }⟩
  · intro M U x
    simpa [sectionTensor, pure, Adjunction.homEquiv_unit] using
      hA M (p.ordinary.obj M) (eqToHom (p.obj_eq M).symm) U x
  · intro P hP hf
    have h := hd ((HomotopyCategory.quotient _ _).obj P)
      ((p.ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) (𝟙 _)
    rw [Adjunction.homEquiv_id] at h
    have h' := congrArg (fun f ↦ f ≫
      (restriction a).mapDerivedCategoryFactorsh.hom.app _) h
    simpa [Adjunction.homEquiv_unit, Category.assoc] using h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private noncomputable def resComp {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) : restriction b ⋙ restriction a ≅ restriction (a ≫ b) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction a).obj ((restriction b).obj M)).val.obj U)
        (Y := ((restriction (a ≫ b)).obj M).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction (a ≫ b)).obj M).val.obj U)
        (Y := ((restriction a).obj ((restriction b).obj M)).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl
  }) (by intros; ext; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
set_option linter.unusedSectionVars false in
private theorem sectionTensor_smul_one {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation a) (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) : sectionTensor p M U s x = s • sectionTensor p M U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (changeOfRingsPresheaf a M)
  change (eqToHom (p.obj_eq M).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)) =
    s • (eqToHom (p.obj_eq M).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
  rw [← ((eqToHom (p.obj_eq M).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
    (s * 1) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x
  rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private noncomputable def ordinaryComp
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (A : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).ordinary ⊣ restriction a)
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    (p a).ordinary ⋙ (p b).ordinary ≅ (p (a ≫ b)).ordinary :=
  (((A a).comp (A b)).ofNatIsoRight (resComp a b)).leftAdjointUniq (A (a ≫ b))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
set_option linter.unusedSectionVars false in
private theorem ordinaryComp_unit
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (A : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).ordinary ⊣ restriction a)
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) (M : Modules R) :
    (A a).unit.app M ≫ (restriction a).map ((A b).unit.app ((p a).ordinary.obj M)) ≫
      (resComp a b).hom.app ((p b).ordinary.obj ((p a).ordinary.obj M)) ≫
      (restriction (a ≫ b)).map ((ordinaryComp p A a b).hom.app M) =
      (A (a ≫ b)).unit.app M := by
  simpa only [ordinaryComp, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using
    Adjunction.unit_leftAdjointUniq_hom_app
      (((A a).comp (A b)).ofNatIsoRight (resComp a b)) (A (a ≫ b)) M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem ordinaryComp_hom
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (A : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).ordinary ⊣ restriction a)
    (hA : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
      (U : Cᵒᵖ) (x : M.val.obj U),
      ((A a).unit.app M).val.app U x = sectionTensor (p a) M U 1 x)
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U) :
    ((ordinaryComp p A a b).hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p (a ≫ b)) M U ((b.hom.app U).hom s * t) x := by
  have hu := congrArg (fun f ↦ f.val.app U x) (ordinaryComp_unit p A a b M)
  change ((ordinaryComp p A a b).hom.app M).val.app U
    (((A b).unit.app ((p a).ordinary.obj M)).val.app U
      (((A a).unit.app M).val.app U x)) = _ at hu
  simp only [hA] at hu
  have hs : sectionTensor (p b) ((p a).ordinary.obj M) U 1
      (s • sectionTensor (p a) M U 1 x) =
      (b.hom.app U).hom s • sectionTensor (p b) ((p a).ordinary.obj M) U 1
        (sectionTensor (p a) M U 1 x) := by
    have hm := (((A b).unit.app ((p a).ordinary.obj M)).val.app U).hom.map_smul s
      (sectionTensor (p a) M U 1 x)
    change (((A b).unit.app ((p a).ordinary.obj M)).val.app U)
        (s • sectionTensor (p a) M U 1 x) =
      (b.hom.app U).hom s •
        (show ((p b).ordinary.obj ((p a).ordinary.obj M)).val.obj U from
          (((A b).unit.app ((p a).ordinary.obj M)).val.app U)
            (sectionTensor (p a) M U 1 x)) at hm
    exact (hA b _ U _).symm.trans (hm.trans
      (congrArg (fun y : ((p b).ordinary.obj ((p a).ordinary.obj M)).val.obj U ↦
        (b.hom.app U).hom s • y) (hA b _ U _)))
  rw [sectionTensor_smul_one (p a), sectionTensor_smul_one (p b), hs]
  rw [((ordinaryComp p A a b).hom.app M).val.app U |>.hom.map_smul,
    ((ordinaryComp p A a b).hom.app M).val.app U |>.hom.map_smul, hu]
  rw [sectionTensor_smul_one, smul_smul, mul_comm t]
  exact congrArg (fun y : ((p (a ≫ b)).ordinary.obj M).val.obj U ↦
    ((b.hom.app U).hom s * t) • y) (hA (a ≫ b) M U x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem ordinaryComp_inv
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (A : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).ordinary ⊣ restriction a)
    (hA : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
      (U : Cᵒᵖ) (x : M.val.obj U),
      ((A a).unit.app M).val.app U x = sectionTensor (p a) M U 1 x)
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U) :
    ((ordinaryComp p A a b).inv.app M).val.app U
      (sectionTensor (p (a ≫ b)) M U t x) =
      sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x) := by
  have h := congrArg (fun y ↦ ((ordinaryComp p A a b).inv.app M).val.app U y)
    (ordinaryComp_hom p A hA a b M U x 1 t)
  simp only [map_one, one_mul] at h
  have hc := congrArg (fun f ↦ f.val.app U
    (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x)))
    ((ordinaryComp p A a b).hom_inv_id_app M)
  exact h.symm.trans hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private local instance exact_comp_limits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private local instance exact_comp_colimits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private noncomputable def rightComp {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) :
    (restriction b).mapDerivedCategory ⋙ (restriction a).mapDerivedCategory ≅
      (restriction (a ≫ b)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (restriction b) (restriction a)) ≪≫
    Functor.mapDerivedCategoryNatIso (resComp a b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem exactComp_assoc
    {A₀ A₁ A₂ A₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian A₃]
    [HasDerivedCategory.{w} A₀] [HasDerivedCategory.{w} A₁]
    [HasDerivedCategory.{w} A₂] [HasDerivedCategory.{w} A₃]
    (F₁₀ : A₁ ⥤ A₀) (F₂₁ : A₂ ⥤ A₁) (F₃₂ : A₃ ⥤ A₂)
    (F₂₀ : A₂ ⥤ A₀) (F₃₁ : A₃ ⥤ A₁) (F₃₀ : A₃ ⥤ A₀)
    [F₁₀.Additive] [PreservesFiniteLimits F₁₀] [PreservesFiniteColimits F₁₀]
    [F₂₁.Additive] [PreservesFiniteLimits F₂₁] [PreservesFiniteColimits F₂₁]
    [F₃₂.Additive] [PreservesFiniteLimits F₃₂] [PreservesFiniteColimits F₃₂]
    [F₂₀.Additive] [PreservesFiniteLimits F₂₀] [PreservesFiniteColimits F₂₀]
    [F₃₁.Additive] [PreservesFiniteLimits F₃₁] [PreservesFiniteColimits F₃₁]
    [F₃₀.Additive] [PreservesFiniteLimits F₃₀] [PreservesFiniteColimits F₃₀]
    (e₀₁₂ : F₂₁ ⋙ F₁₀ ≅ F₂₀) (e₁₂₃ : F₃₂ ⋙ F₂₁ ≅ F₃₁)
    (e₀₁₃ : F₃₁ ⋙ F₁₀ ≅ F₃₀) (e₀₂₃ : F₃₂ ⋙ F₂₀ ≅ F₃₀)
    (h : isoWhiskerLeft F₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ F₁₀ ≪≫ e₀₁₃) :
    isoWhiskerLeft F₃₂.mapDerivedCategory
        ((Functor.mapDerivedCategoryCompIso F₂₁ F₁₀) ≪≫
          Functor.mapDerivedCategoryNatIso e₀₁₂) ≪≫
      ((Functor.mapDerivedCategoryCompIso F₃₂ F₂₀) ≪≫
        Functor.mapDerivedCategoryNatIso e₀₂₃) =
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ((Functor.mapDerivedCategoryCompIso F₃₂ F₂₁) ≪≫
        Functor.mapDerivedCategoryNatIso e₁₂₃) F₁₀.mapDerivedCategory ≪≫
      ((Functor.mapDerivedCategoryCompIso F₃₁ F₁₀) ≪≫
        Functor.mapDerivedCategoryNatIso e₀₁₃) := by
  -- Invert the ordinary coherence square, then transport it through exact derivation.
  have hi : e₀₂₃.symm ≪≫ isoWhiskerLeft F₃₂ e₀₁₂.symm =
      e₀₁₃.symm ≪≫ isoWhiskerRight e₁₂₃.symm F₁₀ := by
    apply Iso.ext
    ext X
    have hx := congrArg (fun e ↦ e.inv.app X) h
    simpa only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, NatTrans.comp_app,
      isoWhiskerLeft_inv,
      isoWhiskerRight_inv, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, Category.assoc] using hx
  have hn := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) hi
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hn
  apply Iso.symm_eq_iff.mp
  apply Iso.ext
  ext X
  have hnX := congrArg (fun t ↦ t.app X) hn
  have hl := congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F₃₂ e₀₁₂.symm) X
  have hr := congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e₁₂₃.symm F₁₀) X
  have hc := congr_app (Functor.mapDerivedCategoryCompIso_assoc F₃₂ F₂₁ F₁₀) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapDerivedCategoryNatIso_symm] at hnX hl hr hc
  simp only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, F₁₀.mapDerivedCategory.map_comp,
    Category.comp_id, Category.assoc]
  -- Naturality moves the ordinary comparisons outside; derived associativity finishes.
  rw [← reassoc_of% hl, ← reassoc_of% hr, hc]
  simp only [← Category.assoc]
  rw [hnX]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem rightComp_assoc {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) :
    isoWhiskerLeft (restriction c).mapDerivedCategory (rightComp a b) ≪≫
      rightComp (a ≫ b) c =
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (rightComp b c) (restriction a).mapDerivedCategory ≪≫
      rightComp a (b ≫ c) := by
  exact exactComp_assoc (restriction a) (restriction b) (restriction c)
    (restriction (a ≫ b)) (restriction (b ≫ c)) (restriction ((a ≫ b) ≫ c))
    (resComp a b) (resComp b c) (resComp a (b ≫ c)) (resComp (a ≫ b) c)
    (by ext M U x; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem rightComp_normalization {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (H : HomotopyCategory (Modules T) (ComplexShape.up ℤ)) :
    (rightComp a b).hom.app (DerivedCategory.Qh.obj H) ≫
      (restriction (a ≫ b)).mapDerivedCategoryFactorsh.hom.app H =
    (restriction a).mapDerivedCategory.map
        ((restriction b).mapDerivedCategoryFactorsh.hom.app H) ≫
      (restriction a).mapDerivedCategoryFactorsh.hom.app
        (((restriction b).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (resComp a b) (ComplexShape.up ℤ)).hom.app H)
    := by
  dsimp only [rightComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh (restriction b) (restriction a)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  congr 2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem rightComp_inverse_normalization {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (H : HomotopyCategory (Modules T) (ComplexShape.up ℤ)) :
    (restriction a).mapDerivedCategoryFactorsh.inv.app
        (((restriction b).mapHomotopyCategory (.up ℤ)).obj H) ≫
      (restriction a).mapDerivedCategory.map
        ((restriction b).mapDerivedCategoryFactorsh.inv.app H) ≫
      (rightComp a b).hom.app (DerivedCategory.Qh.obj H) =
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (resComp a b) (.up ℤ)).hom.app H) ≫
      (restriction (a ≫ b)).mapDerivedCategoryFactorsh.inv.app H := by
  apply (cancel_mono ((restriction (a ≫ b)).mapDerivedCategoryFactorsh.hom.app H)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [rightComp_normalization]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(restriction a).mapDerivedCategory.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private noncomputable def identityInverse (R : Sheaf J CommRingCat.{r}) :
    AlgebraicInverseImage (𝟭 (Sheaf J (Type r))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules R)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem intermediate_computed {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (p : Presentation a) (q : Presentation b)
    (D : AdjData q) (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hf : ∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) :
    IsIso (q.counit.app ((p.ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj P))) := by
  have hp := isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse R) a p.ordinary p.obj_eq p.map_eq P hP hf
  exact D.computed ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) hp.1 hp.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem ordinaryComp_homotopy_unit
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (A : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).ordinary ⊣ restriction a)
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (H : HomotopyCategory (Modules R) (ComplexShape.up ℤ)) :
    ((A a).mapHomotopyCategory (.up ℤ)).unit.app H ≫
      ((restriction a).mapHomotopyCategory (.up ℤ)).map
        (((A b).mapHomotopyCategory (.up ℤ)).unit.app
          (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj H)) ≫
      (Functor.mapHomotopyCategoryCompIso (resComp a b) (.up ℤ)).hom.app
        (((p b).ordinary.mapHomotopyCategory (.up ℤ)).obj
          (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj H)) ≫
      ((restriction (a ≫ b)).mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (ordinaryComp p A a b) (.up ℤ)).hom.app H) =
      ((A (a ≫ b)).mapHomotopyCategory (.up ℤ)).unit.app H := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  have hb := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ) (A b)
    (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [hb]
  change (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ =
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact ordinaryComp_unit p A a b (P.X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private noncomputable def derivedComp
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived :=
  (((D a).derived.comp (D b).derived).ofNatIsoRight (rightComp a b)).leftAdjointUniq
    (D (a ≫ b)).derived

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_eq
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    derivedComp p D a b = Adjunction.leftAdjointCompIso
      (D a).derived (D b).derived (D (a ≫ b)).derived (rightComp a b) := by
  apply Iso.ext
  ext X
  apply ((((D a).derived.comp (D b).derived).ofNatIsoRight
    (rightComp a b)).homEquiv X _).injective
  dsimp only [derivedComp]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit]
  rw [Adjunction.leftAdjointCompIso_hom]
  change _ = (((D a).derived.comp (D b).derived).unit.app X ≫
    ((restriction b).mapDerivedCategory ⋙ (restriction a).mapDerivedCategory).map
      (((conjugateEquiv (D (a ≫ b)).derived
        ((D a).derived.comp (D b).derived)).symm (rightComp a b).inv).app X)) ≫ _
  rw [← unit_conjugateEquiv_symm]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_unit
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (X : DerivedCategory (Modules R)) :
    (D a).derived.unit.app X ≫
      (restriction a).mapDerivedCategory.map ((D b).derived.unit.app ((p a).derived.obj X)) ≫
      (rightComp a b).hom.app ((p b).derived.obj ((p a).derived.obj X)) ≫
      (restriction (a ≫ b)).mapDerivedCategory.map ((derivedComp p D a b).hom.app X) =
      (D (a ≫ b)).derived.unit.app X := by
  simpa only [derivedComp, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using
    Adjunction.unit_leftAdjointUniq_hom_app
      (((D a).derived.comp (D b).derived).ofNatIsoRight (rightComp a b))
      (D (a ≫ b)).derived X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_assoc
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : DerivedCategory (Modules R)) :
    (p c).derived.map ((derivedComp p D a b).hom.app X) ≫
      (derivedComp p D (a ≫ b) c).hom.app X =
    (derivedComp p D b c).hom.app ((p a).derived.obj X) ≫
      (derivedComp p D a (b ≫ c)).hom.app X ≫
      eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (Category.assoc a b c).symm) := by
  have h := Adjunction.leftAdjointCompIso_assoc
    (D a).derived (D b).derived (D c).derived (D (a ≫ b)).derived
    (D (b ≫ c)).derived (D ((a ≫ b) ≫ c)).derived
    (rightComp a b) (rightComp b c) (rightComp a (b ≫ c))
    (rightComp (a ≫ b) c) (rightComp_assoc a b c)
  have hh := congrArg (fun e ↦ e.hom.app X) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    isoWhiskerLeft_hom, Functor.whiskerLeft_app, isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] at hh
  simp only [derivedComp_eq, eqToHom_refl, Category.comp_id]
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_assoc_strict
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : DerivedCategory (Modules R)) :
    (p c).derived.map ((derivedComp p D a b).hom.app X) ≫
      (derivedComp p D (a ≫ b) c).hom.app X =
    (derivedComp p D b c).hom.app ((p a).derived.obj X) ≫
      (derivedComp p D a (b ≫ c)).hom.app X := by
  simpa only [eqToHom_refl, Category.comp_id] using derivedComp_assoc p D a b c X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_transport_left
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T : Sheaf J CommRingCat.{r}} (a a' : R ⟶ S) (b : S ⟶ T)
    (h : a = a') (X : DerivedCategory (Modules R)) :
    (p b).derived.map (eqToHom (congrArg (fun f ↦ (p f).derived.obj X) h)) ≫
      (derivedComp p D a' b).hom.app X =
    (derivedComp p D a b).hom.app X ≫
      eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (congrArg (fun f ↦ f ≫ b) h)) := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_transport_right
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b b' : S ⟶ T)
    (h : b = b') (X : DerivedCategory (Modules R)) :
    eqToHom (congrArg (fun f ↦ (p f).derived.obj ((p a).derived.obj X)) h) ≫
      (derivedComp p D a b').hom.app X =
    (derivedComp p D a b).hom.app X ≫
      eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (congrArg (fun f ↦ a ≫ f) h)) := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_coefficient_naturality
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T R' S' T' : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R' ⟶ S') (b' : S' ⟶ T')
    (α : R ⟶ R') (β : S ⟶ S') (γ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ γ = β ≫ b')
    (hab : (a ≫ b) ≫ γ = α ≫ (a' ≫ b')) (X : DerivedCategory (Modules R)) :
    (p γ).derived.map ((derivedComp p D a b).hom.app X) ≫
      (squareComparison p (derivedComp p D) (a ≫ b) (a' ≫ b') α γ hab).hom.app X =
    (squareComparison p (derivedComp p D) b b' β γ hb).hom.app ((p a).derived.obj X) ≫
      (p b').derived.map ((squareComparison p (derivedComp p D) a a' α β ha).hom.app X) ≫
      (derivedComp p D a' b').hom.app ((p α).derived.obj X) := by
  have hm : (derivedComp p D β b').inv.app ((p a).derived.obj X) ≫
      (p b').derived.map ((derivedComp p D a β).hom.app X) =
      (derivedComp p D a (β ≫ b')).hom.app X ≫
        (derivedComp p D (a ≫ β) b').inv.app X := by
    apply (cancel_mono ((derivedComp p D (a ≫ β) b').hom.app X)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [derivedComp_assoc_strict]
    simp only [Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  apply (cancel_mono ((derivedComp p D α (a' ≫ b')).hom.app X)).1
  simp only [Category.assoc]
  rw [← derivedComp_assoc_strict p D α a' b' X]
  simp only [squareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, (p b').derived.map_comp, Category.assoc]
  simp only [← (p b').derived.map_comp_assoc, Iso.inv_hom_id_app,
    Category.comp_id, (p b').derived.map_id, Category.id_comp]
  rw [(p b').derived.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hm]
  erw [derivedComp_transport_left p D (a ≫ β) (α ≫ a') b' ha X]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% (derivedComp_transport_right p D a (b ≫ γ) (β ≫ b') hb X)]
  rw [reassoc_of% (derivedComp_assoc_strict p D a b γ X)]
  simp only [eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
open CategoryTheory.Functor in
private theorem derivedComp_representative
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a))
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (H : HomotopyCategory (Modules R) (ComplexShape.up ℤ)) :
    (derivedComp p D a b).hom.app (DerivedCategory.Qh.obj H) ≫ (p (a ≫ b)).counit.app H =
      (p b).derived.map ((p a).counit.app H) ≫
        (p b).counit.app (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (ordinaryComp p (fun a ↦ (D a).ordinary) a b) (.up ℤ)).hom.app H) := by
  let A := fun {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) ↦ (D a).ordinary
  let δ := (Functor.mapHomotopyCategoryCompIso (ordinaryComp p A a b) (.up ℤ)).hom.app H
  let g := ((A b).mapHomotopyCategory (.up ℤ)).homEquiv _ _ δ
  have ho : ((A a).mapHomotopyCategory (.up ℤ)).homEquiv _ _ g ≫
      (Functor.mapHomotopyCategoryCompIso (resComp a b) (.up ℤ)).hom.app
        (((p (a ≫ b)).ordinary.mapHomotopyCategory (.up ℤ)).obj H) =
      ((A (a ≫ b)).mapHomotopyCategory (.up ℤ)).unit.app H := by
    dsimp only [g]
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [((restriction a).mapHomotopyCategory (.up ℤ)).map_comp]
    simp only [Category.assoc]
    erw [(Functor.mapHomotopyCategoryCompIso (resComp a b) (.up ℤ)).hom.naturality δ]
    exact ordinaryComp_homotopy_unit p A a b H
  let ac := ((D a).derived.comp (D b).derived).ofNatIsoRight (rightComp a b)
  apply (ac.homEquiv _ _).injective
  rw [ac.homEquiv_naturality_right]
  change (ac.homEquiv _ _ ((ac.leftAdjointUniq (D (a ≫ b)).derived).hom.app _)) ≫
    (restriction (a ≫ b)).mapDerivedCategory.map ((p (a ≫ b)).counit.app H) = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (D (a ≫ b)).derived.homEquiv _ _ ((p (a ≫ b)).counit.app H) = _
  have hab := (D (a ≫ b)).hom_comparison H
    (((p (a ≫ b)).ordinary.mapHomotopyCategory (.up ℤ)).obj H) (𝟙 _)
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hab
  erw [Adjunction.homEquiv_id] at hab
  erw [hab]
  dsimp only [ac]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change _ = (D a).derived.homEquiv _ _ ((D b).derived.homEquiv _ _
    ((p b).derived.map ((p a).counit.app H) ≫ _)) ≫ _
  rw [Adjunction.homEquiv_naturality_left]
  erw [(D b).hom_comparison]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  erw [(D a).hom_comparison]
  simp only [Category.assoc]
  erw [rightComp_inverse_normalization]
  erw [← DerivedCategory.Qh.map_comp_assoc, ho]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
/-- Successive derived scalar extensions have their canonical tensor comparison, inverse,
unit normalization, coefficient naturality and coherent finite iteration. This is a
family statement, so naturality concerns arbitrary derived morphisms as well as changing
coefficient rings. No ring map is required to be flat or surjective, and no complex is
required to be bounded. Ordinary rings are the specialization to the singleton category
with the bottom (identity-cover) topology.

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YS, 06YY and 07A6
(auxiliary; not a blueprint node).

Proof:
1. Use lem-pur-derived-change-of-rings to present each ordinary extension and its
universal unbounded left-derived pair. Resolve each input by a flat-term K-flat complex
using lem-pc-kflat-resolution (06YS), without assuming functorial resolutions.
2. By lem-weil-pbc-ringed-topos-kflat-pullback (0G7E), applied to identity inverse image,
the first and successive ordinary extensions remain flat-term K-flat; 06YY computes the
derived extensions by these complexes and preserves quasi-isomorphisms between them.
3. On sections define the two maps by the formulas in ordinary_hom and ordinary_inv.
Balancing over R uses b(a(r)s)=b(a(r))b(s); balancing over S uses multiplicativity of b.
The inverse moves the middle scalar across the outer tensor. Restrictions commute with
these formulas. The section calculus of def-weil-pbc-ringed-tensor-section-calculus
and the actual sheafification construction of def-pur-sheaf-tensor-product show that
they are mutually inverse sheaf morphisms. They commute with the complex differential.
4. These maps are natural for termwise morphisms, hence also homotopies. Apply the
flat-term K-flat localization equivalence of lem-weil-pbc-site-derived-tensor-descent
and clauses (2),(3) of lem-weil-pbc-localization-universal-property to descend the
comparison and its inverse. The universal 06YY counits give representative exactly;
uniqueness makes this independent of the resolution and all comparison choices.
5. Use lem-pur-sheaf-ring-derived-coefficient-adjunction (07A6) to normalize ordinary
and derived units. The composite sends x to 1 tensor (1 tensor x), which the comparison
sends to 1 tensor x. Exact restriction leaves underlying sheaves unchanged. Descent and
naturality give unit_comp at every derived input.
6. On triple tensors both collapses multiply the images of all scalars in the final
ring, in order. Multiplicativity and associativity give associative; induction on
parenthesizations gives every finite iteration, including identity ring maps.
7. In a commuting coefficient diagram the two formulas agree because b' beta=gamma b
and all vertical maps preserve one. Compute derived coefficient change using the
flat-term K-flat complex P tensor_R R'. Localization preserves these identities;
associative gives the displayed coefficient_naturality pasting equation.
8. On the singleton identity-cover site sheafification is identity and module sheaves
are ordinary modules. Thus the same statement includes ordinary, possibly nonflat,
quotient maps, zero coefficients and unbounded complexes. -/
theorem successive_derived_quotient_normalization :
    ∃ p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a,
      Nonempty (Normalization p) := by
  -- Construct comparisons by normalized adjoint uniqueness. The helpers above verify
  -- the tensor formulas, the universal-counit representative, and all coherence laws.
  -- The accompanying DAG records this shorter route through the existing Hom comparison.
  classical
  let p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a :=
    fun a ↦ Classical.choice (presentation_exists a)
  let D : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), AdjData (p a) :=
    fun a ↦ Classical.choice (adjData_exists (p a))
  let A := fun {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) ↦ (D a).ordinary
  refine ⟨p, ⟨{
    ordinary := ordinaryComp p A
    ordinary_hom := ordinaryComp_hom p A (fun a ↦ (D a).ordinary_unit)
    ordinary_inv := ordinaryComp_inv p A (fun a ↦ (D a).ordinary_unit)
    derived := derivedComp p D
    computed := fun a ↦ (D a).computed
    intermediate_computed := fun a b ↦ intermediate_computed a b (p a) (p b) (D b)
    representative := fun a b P _ _ ↦ derivedComp_representative p D a b
      ((HomotopyCategory.quotient _ _).obj P)
    ordinaryAdjunction := A
    ordinary_unit := fun a ↦ (D a).ordinary_unit
    right := fun a ↦ (restriction a).mapDerivedCategory
    right_factors := fun a ↦ (restriction a).mapDerivedCategoryFactorsh
    adjunction := fun a ↦ (D a).derived
    adjunction_normalization := fun a ↦ (D a).unit_normalization
    restrictionComp := resComp
    restrictionComp_sections := by intros; rfl
    rightComp := rightComp
    rightComp_normalization := rightComp_normalization
    unit_comp := derivedComp_unit p D
    associative := derivedComp_assoc p D
    coefficient_naturality := derivedComp_coefficient_naturality p D
  }⟩⟩

end SheafOfModules.SuccessiveDerivedQuotient
