/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionTotalOplaxComparisonData
import all WeilConjectures.AlgebraicGeometry.SectionOrdinaryOplaxNormalization

/-! # The actual internal total oplax arrow in section modules

Source: Stacks Project, Cohomology on Sites, Tag 07A4, displayed total comparison;
Modules on Sites, Tag 03EL (auxiliary; not a blueprint node).

All tensors are relative to the pulled-back coefficient ring. The totalization is the
existing signed direct-sum total, including its infinite degreewise sums. The helpers
name existing functors and canonical comparisons; the final proposition records their
specified-map equalities before and after homotopy quotient and localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
/-- Equality of specified chain maps and of their homotopy and derived images.
Source: Stacks 07A4 and 03EL (auxiliary; not a blueprint node). -/
def TotalMapAgreement (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (modules Λ X)]
    {P Q : CochainComplex (modules Λ X) ℤ} (a b : P ⟶ Q) : Prop :=
  a = b ∧
    (HomotopyCategory.quotient (modules Λ X) (.up ℤ)).map a =
      (HomotopyCategory.quotient (modules Λ X) (.up ℤ)).map b ∧
    DerivedCategory.Q.map a = DerivedCategory.Q.map b

set_option backward.isDefEq.respectTransparency true

-- One proposition records the component, local-generator and localized equations.
/-- The clauses of actual internal-to-section total normalization: tensor and inverse
equalities, both inverse laws, every summand, local scalar formulas, signed differential,
unit multiplication, naturality and the three constraint diagrams. All complex arguments
are arbitrary integer-indexed complexes; flat-term K-flat subcategories introduced in
the node are context for later derived-tensor computation and impose no restriction here.
Source: Stacks 07A4 and 03EL (auxiliary; not a blueprint node). -/
def SectionTotalNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (modules Λ X)] : Prop :=
  (∀ P Q : CochainComplex (internalModules Λ Y) ℤ,
    TotalMapAgreement Λ X (conjugatedInternalTotalIso Λ f P Q).hom
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).hom ) ∧
  (∀ P Q : CochainComplex (internalModules Λ Y) ℤ,
    TotalMapAgreement Λ X (conjugatedInternalTotalIso Λ f P Q).inv
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).inv ) ∧
  (∀ (P Q : CochainComplex (modules Λ Y) ℤ) (p q n : ℤ) (h : p + q = n),
    (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (sectionTotalIso Λ f P Q).hom.f n =
      normalizationSectionTensor Λ f (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ) ∧
  (∀ (P Q : CochainComplex (modules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj
        ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ≫
        (sectionTotalIso Λ f P Q).inv.f n =
      inv (normalizationSectionTensor Λ f (P.X p) (Q.X q)) ≫
        (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ) ∧
  (∀ (P Q : CochainComplex (internalModules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
      (x : ((normalizationInverseImage Λ f).obj (P.X p)).X.obj.obj W)
      (y : ((normalizationInverseImage Λ f).obj (Q.X q)).X.obj.obj W),
    (((CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (actualInternalTotalIso Λ f P Q).hom.f n).hom.hom.app W)
        (normalizationScalarTensor Λ f (P.X p ⊗ Q.X q) W s
          (normalizationInverseImageTensor Λ f (P.X p) (Q.X q) W x y)) =
      ((HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q)
          p q n h).hom.hom.app W)
        (internalPureTensor Λ X
          ((CondensedRing.upperStar Λ f).obj (P.X p))
          ((CondensedRing.upperStar Λ f).obj (Q.X q)) W
          (normalizationScalarTensor Λ f (P.X p) W s x)
          (normalizationScalarTensor Λ f (Q.X q) W 1 y))) ∧
  (∀ (P Q : CochainComplex (internalModules Λ Y) ℤ)
      (p q n : ℤ) (h : p + q = n) (W : X.ProEtᵒᵖ) (s t : (ring Λ X).obj.obj W)
      (x : ((normalizationInverseImage Λ f).obj (P.X p)).X.obj.obj W)
      (y : ((normalizationInverseImage Λ f).obj (Q.X q)).X.obj.obj W),
    ((HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) p q n h ≫
        (actualInternalTotalIso Λ f P Q).inv.f n).hom.hom.app W)
        (internalPureTensor Λ X
          ((CondensedRing.upperStar Λ f).obj (P.X p))
          ((CondensedRing.upperStar Λ f).obj (Q.X q)) W
          (normalizationScalarTensor Λ f (P.X p) W s x)
          (normalizationScalarTensor Λ f (Q.X q) W t y)) =
      (((CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h)).hom.hom.app W)
        (normalizationScalarTensor Λ f (P.X p ⊗ Q.X q) W (s * t)
          (normalizationInverseImageTensor Λ f (P.X p) (Q.X q) W x y))) ∧
  (TotalMapAgreement Λ X
    (conjugatedInternalTotalUnit Λ f) (sectionTotalUnit Λ f) ) ∧
  (∀ (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
      (r : ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)).obj.obj W),
    (((actualInternalTotalUnit Λ f).f 0).hom.hom.app W)
        (normalizationScalarTensor Λ f (𝟙_ (internalModules Λ Y)) W s r) =
      s * (@id ((ring Λ X).obj.obj W) ((condensedPullbackHom Λ f).hom.app W r)) ) ∧
  (∀ (P Q P' Q' : CochainComplex (modules Λ Y) ℤ)
      (a : P ⟶ P') (b : Q ⟶ Q'),
    TotalMapAgreement Λ X
      ((totalSectionPull Λ f).map (a ⊗ₘ b) ≫ (sectionTotalIso Λ f P' Q').hom)
      ((sectionTotalIso Λ f P Q).hom ≫
        ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b)) ) ∧
  (∀ P Q H : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((totalSectionPull Λ f).map (α_ P Q H).hom ≫
        (sectionTotalIso Λ f P (Q ⊗ H)).hom ≫
        (totalSectionPull Λ f).obj P ◁ (sectionTotalIso Λ f Q H).hom)
      ((sectionTotalIso Λ f (P ⊗ Q) H).hom ≫
        (sectionTotalIso Λ f P Q).hom ▷ (totalSectionPull Λ f).obj H ≫
        (α_ ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q)
          ((totalSectionPull Λ f).obj H)).hom) ) ∧
  (∀ P : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((sectionTotalIso Λ f (𝟙_ (CochainComplex (modules Λ Y) ℤ)) P).hom ≫
        sectionTotalUnit Λ f ▷ (totalSectionPull Λ f).obj P ≫
        (λ_ ((totalSectionPull Λ f).obj P)).hom)
      ((totalSectionPull Λ f).map (λ_ P).hom) ) ∧
  (∀ P : CochainComplex (modules Λ Y) ℤ,
    TotalMapAgreement Λ X
      ((sectionTotalIso Λ f P (𝟙_ (CochainComplex (modules Λ Y) ℤ))).hom ≫
        (totalSectionPull Λ f).obj P ◁ sectionTotalUnit Λ f ≫
        (ρ_ ((totalSectionPull Λ f).obj P)).hom)
      ((totalSectionPull Λ f).map (ρ_ P).hom)
)

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] DerivedCategory.Q HomotopyCategory.quotient
attribute [local irreducible] totalComparison ordinaryTensorComparison ordinaryUnitComparison
attribute [local irreducible] internalPullOplax CondensedRing.monoidal_upperStar
attribute [local irreducible] normalizationScalarTensor normalizationInverseImageTensor
attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence
  InternalAbelianSheafModule.sectionModuleFunctor InternalModuleOperations.upperComparison

attribute [local irreducible] CondensedRing.upperStar
  ProEtale.upperStar ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf

private theorem inverse_restriction {C : Type*} [Category* C] {A B U V : C}
    (i : U ⟶ A) (j : V ⟶ B) (a : A ⟶ B) (a' : B ⟶ A)
    (d : U ⟶ V) (d' : V ⟶ U) (ha : a ≫ a' = 𝟙 A) (hd : d' ≫ d = 𝟙 V)
    (h : i ≫ a = d ≫ j) : j ≫ a' = d' ≫ i := by
  calc
    j ≫ a' = d' ≫ (d ≫ j) ≫ a' := by
      simp only [← Category.assoc, hd, Category.id_comp]
    _ = d' ≫ (i ≫ a) ≫ a' := by rw [h]
    _ = d' ≫ i := by simp only [Category.assoc, ha, Category.comp_id]

private theorem iso_inverse_eq {C : Type*} [Category* C] {X Y : C}
    (e e' : X ≅ Y) (h : e.hom = e'.hom) : e.inv = e'.inv :=
  congrArg Iso.inv (Iso.ext h)

section PastingSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

private theorem paste_summand_square
    (E : A ⥤ C) (E' : B ⥤ D) (F : A ⥤ B) (F' : C ⥤ D)
    (a : F ⋙ E' ≅ E ⋙ F') {x T : A} {b B₀ : B} {c C₀ : C} {d d' U V : D}
    (j : x ⟶ T) (i : F.obj T ⟶ B₀) (t : E.obj T ⟶ C₀)
    (t' : E'.obj B₀ ⟶ U) (s : F'.obj C₀ ⟶ V) (e : U ⟶ V)
    (di : F.obj x ⟶ b) (d₀ : E.obj x ⟶ c)
    (d₁ : E'.obj b ⟶ d) (ds : F'.obj c ⟶ d')
    (jF : b ⟶ B₀) (jE : c ⟶ C₀) (jEF : d ⟶ U) (jFE : d' ⟶ V) (v : d ⟶ d')
    (hi : F.map j ≫ i = di ≫ jF) (ht : E.map j ≫ t = d₀ ≫ jE)
    (ht' : E'.map jF ≫ t' = d₁ ≫ jEF) (hs : F'.map jE ≫ s = ds ≫ jFE)
    (he : jEF ≫ e = v ≫ jFE)
    (ho : E'.map di ≫ d₁ ≫ v = a.hom.app x ≫ F'.map d₀ ≫ ds) :
    E'.map (F.map j) ≫ E'.map i ≫ t' ≫ e =
      E'.map (F.map j) ≫ a.hom.app T ≫ F'.map t ≫ s := by
  rw [← E'.map_comp_assoc, hi, E'.map_comp, Category.assoc, reassoc_of% ht', he]
  rw [reassoc_of% (a.hom.naturality j)]
  change _ = a.hom.app x ≫ F'.map (E.map j) ≫ F'.map t ≫ s
  rw [← F'.map_comp_assoc, ht, F'.map_comp, Category.assoc, hs]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ jFE) ho

private theorem cancel_conjugation {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {x y : A} {z w : B} (t : x ≅ y) (r : z ≅ F.obj x)
    (i : z ⟶ w) (s : F.obj y ⟶ w)
    (h : i = r.hom ≫ F.map t.hom ≫ s) : F.map t.inv ≫ r.inv ≫ i = s := by
  rw [h, Iso.inv_hom_id_assoc, ← F.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem section_conjugation_hom_eq {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) (G : C ⥤ B) {x y : A} {u v : C} {w t : B}
    (p : x ≅ y) (r : G.obj u ≅ F.obj x) (i : u ≅ v)
    (c : G.obj v ≅ w) (e : w ≅ t) (s : F.obj y ⟶ t)
    (h : G.map i.hom ≫ c.hom ≫ e.hom = r.hom ≫ F.map p.hom ≫ s) :
    (sectionConjugationIso F G p r i c e).hom = s := by
  unfold sectionConjugationIso
  exact cancel_conjugation F p r _ s h

end PastingSquare

section GenericOplaxLaws

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]

private def OplaxLawBundle (F : C ⥤ D)
    (b : ∀ P Q, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ D) : Prop :=
    (∀ (P Q P' Q' : C) (a : P ⟶ P') (a' : Q ⟶ Q'),
      F.map (a ⊗ₘ a') ≫ b P' Q' = b P Q ≫ (F.map a ⊗ₘ F.map a')) ∧
    (∀ P Q H : C,
      F.map (α_ P Q H).hom ≫ b P (Q ⊗ H) ≫ F.obj P ◁ b Q H =
        b (P ⊗ Q) H ≫ b P Q ▷ F.obj H ≫ (α_ (F.obj P) (F.obj Q) (F.obj H)).hom) ∧
    (∀ P : C, b (𝟙_ C) P ≫ u ▷ F.obj P ≫ (λ_ (F.obj P)).hom =
      F.map (λ_ P).hom) ∧
    (∀ P : C, b P (𝟙_ C) ≫ F.obj P ◁ u ≫ (ρ_ (F.obj P)).hom =
      F.map (ρ_ P).hom)

private theorem oplax_laws (F : C ⥤ D) [F.OplaxMonoidal]
    (b : ∀ P Q, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (hb : ∀ P Q, b P Q = Functor.OplaxMonoidal.δ F P Q)
    (hu : u = Functor.OplaxMonoidal.η F) :
    OplaxLawBundle F b u := by
  unfold OplaxLawBundle
  simp only [hb, hu]
  exact ⟨fun _ _ _ _ a a' ↦ (Functor.OplaxMonoidal.δ_natural F a a').symm,
    fun P Q H ↦ (Functor.OplaxMonoidal.associativity F P Q H).symm,
    Functor.OplaxMonoidal.left_unitality_hom F,
    Functor.OplaxMonoidal.right_unitality_hom F⟩

end GenericOplaxLaws

private theorem mapped_equalities {A B C : Sort*} (F : A → B) (G : A → C)
    {a b : A} (h : a = b) : a = b ∧ F a = F b ∧ G a = G b :=
  ⟨h, congrArg F h, congrArg G h⟩

private theorem total_agreement {X : Scheme.{u}}
    [HasDerivedCategory.{u + 1} (modules Λ X)]
    {P Q : CochainComplex (modules Λ X) ℤ} {a b : P ⟶ Q} (h : a = b) :
    TotalMapAgreement Λ X a b := by
  exact mapped_equalities ((HomotopyCategory.quotient (modules Λ X) (.up ℤ)).map)
    DerivedCategory.Q.map h

private theorem section_total_summands {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) (p q n : ℤ) (h : p + q = n) :
    ((pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (sectionTotalIso Λ f P Q).hom.f n =
      normalizationSectionTensor Λ f (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h) ∧
    (HomologicalComplex.ιTensorObj
        ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h ≫
        (sectionTotalIso Λ f P Q).inv.f n =
      inv (normalizationSectionTensor Λ f (P.X p) (Q.X q)) ≫
        (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h)) := by
  have forward :
      (pullback Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
          (sectionTotalIso Λ f P Q).hom.f n =
        normalizationSectionTensor Λ f (P.X p) (Q.X q) ≫
          HomologicalComplex.ιTensorObj
            ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) p q n h := by
    rw [sectionTotalIso_hom]
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (.up ℤ) P Q p q n h
  have : IsIso (normalizationSectionTensor Λ f (P.X p) (Q.X q)) := by
    unfold normalizationSectionTensor
    infer_instance
  refine ⟨forward, ?_⟩
  refine inverse_restriction _ _ _ _ _ _ ?_
    (IsIso.inv_hom_id (normalizationSectionTensor Λ f (P.X p) (Q.X q))) forward
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun k ↦ k.f n) (sectionTotalIso Λ f P Q).hom_inv_id

private theorem internal_tensor_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f) M N =
      normalizationInternalTensor Λ f M N := by
  unfold normalizationInternalTensor
  exact congrArg (fun t : (CondensedRing.upperStar Λ f).OplaxMonoidal ↦ t.δ M N)
    (totalInternalOplax_eq Λ f)

private theorem internal_total_summand {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) (p q n : ℤ) (h : p + q = n) :
    (CondensedRing.upperStar Λ f).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (actualInternalTotalIso Λ f P Q).hom.f n =
      normalizationInternalTensor Λ f (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) p q n h := by
  rw [actualInternalTotalIso_hom]
  have hs := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans (CondensedRing.upperStar Λ f)) (.up ℤ) P Q p q n h
  simp only [HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.mapBifunctorComparisonApp,
    Functor.OplaxMonoidal.δNatTrans_app_app, internal_tensor_normalized] at hs ⊢
  convert! hs using 1

private theorem internal_total_inverse_summand {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj
        ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) p q n h ≫
        (actualInternalTotalIso Λ f P Q).inv.f n =
      normalizationInternalTensorInv Λ f (P.X p) (Q.X q) ≫
        (CondensedRing.upperStar Λ f).map
          (HomologicalComplex.ιTensorObj P Q p q n h) := by
  let := CondensedRing.monoidal_upperStar Λ f
  refine inverse_restriction _ _ _ _ _ _ ?_ ?_
    (internal_total_summand Λ f P Q p q n h)
  · simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun k ↦ k.f n) (actualInternalTotalIso Λ f P Q).hom_inv_id
  · unfold normalizationInternalTensorInv normalizationInternalTensor
    change ((CondensedRing.monoidal_upperStar Λ f).toLaxMonoidal.μ _ _ ≫
      (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ _ _) = 𝟙 _
    exact Functor.Monoidal.μ_δ _ _ _

private theorem section_constraint_laws {X Y : Scheme.{u}} (f : X ⟶ Y) :
    OplaxLawBundle (totalSectionPull Λ f) (fun P Q ↦ (sectionTotalIso Λ f P Q).hom)
      (sectionTotalUnit Λ f) := by
  exact oplax_laws (totalSectionPull Λ f) (fun P Q ↦ (sectionTotalIso Λ f P Q).hom)
    (sectionTotalUnit Λ f)
    (sectionTotalIso_δ Λ f) (sectionTotalUnit_η Λ f)

private theorem equivalence_total_summand (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) (p q n : ℤ) (h : p + q = n) :
    (equivalence Λ X).functor.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (totalTensorComparison Λ X P Q).hom.f n =
      (ordinaryTensorComparison Λ X (P.X p) (Q.X q)).hom ≫
        HomologicalComplex.ιTensorObj
          ((totalSectionEquivalence Λ X).obj P)
          ((totalSectionEquivalence Λ X).obj Q) p q n h := by
  unfold totalTensorComparison cochainTensorComparison totalComparison
  exact (totalComparison_existsUnique Λ X P Q).exists.choose_spec p q n h

private theorem termwise_pull_hom_f {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internalModules Λ Y) ℤ) (n : ℤ) :
    (termwisePullComparison Λ f P).hom.f n = (pullComparison Λ f).hom.app (P.X n) := by
  unfold termwisePullComparison
  rfl

-- The coproduct square compares several dependent tensor components.
private theorem tensor_total_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (totalSectionEquivalence Λ X).map (actualInternalTotalIso Λ f P Q).hom ≫
        (totalTensorComparison Λ X ((totalInternalPull Λ f).obj P)
          ((totalInternalPull Λ f).obj Q)).hom ≫
        (tensorIso (termwisePullComparison Λ f P) (termwisePullComparison Λ f Q)).hom =
      (termwisePullComparison Λ f (P ⊗ Q)).hom ≫
        (totalSectionPull Λ f).map (totalTensorComparison Λ Y P Q).hom ≫
        (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
          ((totalSectionEquivalence Λ Y).obj Q)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [termwise_pull_hom_f Λ f (P ⊗ Q) n]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (K₁ := P) (K₂ := Q) (F := curriedTensor (internalModules Λ Y))
    (c := ComplexShape.up ℤ) (j := n)
    (CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor)
  intro p q h
  refine paste_summand_square (equivalence Λ Y).functor (equivalence Λ X).functor
    (CondensedRing.upperStar Λ f) (pullback Λ f) (pullComparison Λ f)
    (x := P.X p ⊗ Q.X q) (T := (P ⊗ Q).X n)
    (b := (CondensedRing.upperStar Λ f).obj (P.X p) ⊗
      (CondensedRing.upperStar Λ f).obj (Q.X q))
    (B₀ := ((totalInternalPull Λ f).obj P ⊗ (totalInternalPull Λ f).obj Q).X n)
    (c := (equivalence Λ Y).functor.obj (P.X p) ⊗
      (equivalence Λ Y).functor.obj (Q.X q))
    (C₀ := ((totalSectionEquivalence Λ Y).obj P ⊗
      (totalSectionEquivalence Λ Y).obj Q).X n)
    (d := (equivalence Λ X).functor.obj ((CondensedRing.upperStar Λ f).obj (P.X p)) ⊗
      (equivalence Λ X).functor.obj ((CondensedRing.upperStar Λ f).obj (Q.X q)))
    (d' := (pullback Λ f).obj ((equivalence Λ Y).functor.obj (P.X p)) ⊗
      (pullback Λ f).obj ((equivalence Λ Y).functor.obj (Q.X q)))
    (U := ((totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj P) ⊗
      (totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj Q)).X n)
    (V := ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P) ⊗
      (totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj Q)).X n)
    (HomologicalComplex.ιTensorObj P Q p q n h)
    ((actualInternalTotalIso Λ f P Q).hom.f n) ((totalTensorComparison Λ Y P Q).hom.f n)
    ((totalTensorComparison Λ X ((totalInternalPull Λ f).obj P)
      ((totalInternalPull Λ f).obj Q)).hom.f n)
    ((sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
      ((totalSectionEquivalence Λ Y).obj Q)).hom.f n) _
    (normalizationInternalTensor Λ f (P.X p) (Q.X q))
    ((ordinaryTensorComparison Λ Y (P.X p) (Q.X q)).hom)
    ((ordinaryTensorComparison Λ X ((CondensedRing.upperStar Λ f).obj (P.X p))
      ((CondensedRing.upperStar Λ f).obj (Q.X q))).hom)
    (normalizationSectionTensor Λ f ((equivalence Λ Y).functor.obj (P.X p))
      ((equivalence Λ Y).functor.obj (Q.X q)))
    (HomologicalComplex.ιTensorObj
      ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q) p q n h)
    (HomologicalComplex.ιTensorObj
      ((totalSectionEquivalence Λ Y).obj P) ((totalSectionEquivalence Λ Y).obj Q) p q n h)
    (HomologicalComplex.ιTensorObj
      ((totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj P))
      ((totalSectionEquivalence Λ X).obj ((totalInternalPull Λ f).obj Q)) p q n h)
    (HomologicalComplex.ιTensorObj
      ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj P))
      ((totalSectionPull Λ f).obj ((totalSectionEquivalence Λ Y).obj Q)) p q n h)
    ((pullComparison Λ f).hom.app (P.X p) ⊗ₘ (pullComparison Λ f).hom.app (Q.X q))
    (internal_total_summand Λ f P Q p q n h) (equivalence_total_summand Λ Y P Q p q n h)
    (equivalence_total_summand Λ X ((totalInternalPull Λ f).obj P)
      ((totalInternalPull Λ f).obj Q) p q n h)
    ((section_total_summands Λ f ((totalSectionEquivalence Λ Y).obj P)
      ((totalSectionEquivalence Λ Y).obj Q) p q n h).1) ?_
    ((ordinaryMate_transport Λ f).1 (P.X p) (Q.X q))
  change HomologicalComplex.ιTensorObj _ _ p q n h ≫
      (HomologicalComplex.mapBifunctorMap (termwisePullComparison Λ f P).hom
        (termwisePullComparison Λ f Q).hom (curriedTensor (modules Λ X)) (.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [termwise_pull_hom_f]
  dsimp only [curriedTensor]
  rw [MonoidalCategory.tensorHom_def]
  exact (Category.assoc _ _ _).symm

-- The concrete categorical transport has several nested functor and tensor projections.
private theorem conjugated_total_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (internalModules Λ Y) ℤ) :
    (conjugatedInternalTotalIso Λ f P Q).hom =
      (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
        ((totalSectionEquivalence Λ Y).obj Q)).hom := by
  unfold conjugatedInternalTotalIso
  exact section_conjugation_hom_eq (totalSectionPull Λ f) (totalSectionEquivalence Λ X)
    (totalTensorComparison Λ Y P Q) (termwisePullComparison Λ f (P ⊗ Q))
    (actualInternalTotalIso Λ f P Q)
    (totalTensorComparison Λ X ((totalInternalPull Λ f).obj P) ((totalInternalPull Λ f).obj Q))
    (tensorIso (termwisePullComparison Λ f P) (termwisePullComparison Λ f Q))
    (sectionTotalIso Λ f ((totalSectionEquivalence Λ Y).obj P)
      ((totalSectionEquivalence Λ Y).obj Q)).hom (tensor_total_square Λ f P Q)

private theorem conjugated_total_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    conjugatedInternalTotalUnit Λ f = sectionTotalUnit Λ f := by
  have unit_total_square :
      (totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
          (totalUnitComparison Λ X).hom =
        (termwisePullComparison Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ))).hom ≫
          (totalSectionPull Λ f).map (totalUnitComparison Λ Y).hom ≫
          sectionTotalUnit Λ f := by
    ext n : 1
    by_cases hn : n = 0
    · subst n
      unfold actualInternalTotalUnit totalUnitComparison termwisePullComparison sectionTotalUnit
      change (equivalence Λ X).functor.map (normalizationInternalUnit Λ f) ≫
          (ordinaryUnitComparison Λ X).hom =
        (pullComparison Λ f).hom.app (𝟙_ (internalModules Λ Y)) ≫
          (pullback Λ f).map (ordinaryUnitComparison Λ Y).hom ≫
          normalizationSectionUnit Λ f
      exact (ordinaryMate_transport Λ f).2
    · exact ((equivalence Λ X).functor.map_isZero
        ((CondensedRing.upperStar Λ f).map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
            (𝟙_ (internalModules Λ Y)) n hn))).eq_of_src _ _
  -- Cancel the source transports using the degreewise square.
  unfold conjugatedInternalTotalUnit
  exact cancel_conjugation (totalSectionPull Λ f) (totalUnitComparison Λ Y)
    (termwisePullComparison Λ f (𝟙_ (CochainComplex (internalModules Λ Y) ℤ)))
    _ _ (unit_total_square)

omit [IsCommMonObj Λ] in
private theorem internal_apply_eq_of_comp (X : Scheme.{u})
    {M N H : internalModules Λ X} (a : M ⟶ H) (b : M ⟶ N) (c : N ⟶ H)
    (hc : a = b ≫ c) (W : X.ProEtᵒᵖ) (x : M.X.obj.obj W) (y : N.X.obj.obj W)
    (hb : (b.hom.hom.app W) x = y) :
    (a.hom.hom.app W) x = (c.hom.hom.app W) y := by
  exact (congrArg (fun k ↦ (k.hom.hom.app W) x) hc).trans
    (congrArg (fun z ↦ (c.hom.hom.app W) z) hb)

-- The twelve dependent comparison clauses share the same signed tensor structures.
/-- Source: Stacks 07A4 and 03EL (auxiliary; not a blueprint node).
Proof: preserve the full coproduct indexed by p+q=n using the specified left adjunctions.
On each summand ordinary oplax normalization identifies the actual internal map with the
ringed comparison, so coproduct uniqueness gives equality in every degree. Naturality
commutes with both differential components, retaining the sign (-1)^p. Scalar splitting
and scalar contraction give the two inverse chain maps. The degree-zero ordinary unit
is scalar multiplication. The existing cochain oplax laws give naturality,
associativity and both unitor identities. Finally apply
the homotopy quotient and derived localization to these equalities, their composites
and identities. No flatness or boundedness has been used. -/
theorem section_oplax_total_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (modules Λ X)] : SectionTotalNormalization Λ f := by
  unfold SectionTotalNormalization
  refine ⟨?_, ?_, (fun P Q p q n h ↦ (section_total_summands Λ f P Q p q n h).1),
    (fun P Q p q n h ↦ (section_total_summands Λ f P Q p q n h).2),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    exact total_agreement Λ (conjugated_total_hom Λ f P Q)
  · intro P Q
    apply total_agreement Λ
    exact iso_inverse_eq _ _ (conjugated_total_hom Λ f P Q)
  · intro P Q p q n h W s x y
    exact internal_apply_eq_of_comp Λ X _ _ _
      (internal_total_summand Λ f P Q p q n h) W _ _
      (forwardTensor_scalar Λ f (P.X p) (Q.X q) W s x y)
  · intro P Q p q n h W s t x y
    exact internal_apply_eq_of_comp Λ X _ _ _
      (internal_total_inverse_summand Λ f P Q p q n h) W _ _
      (inverseTensor_scalar Λ f (P.X p) (Q.X q) W s t x y)
  · exact total_agreement Λ (conjugated_total_unit Λ f)
  · intro W s r
    unfold actualInternalTotalUnit
    change ((normalizationInternalUnit Λ f).hom.hom.app W)
      (normalizationScalarTensor Λ f (𝟙_ (internalModules Λ Y)) W s r) = _
    exact unit_scalar Λ f W s r
  · intro P Q P' Q' a b
    exact total_agreement Λ ((section_constraint_laws Λ f).1 P Q P' Q' a b)
  · intro P Q H
    exact total_agreement Λ ((section_constraint_laws Λ f).2.1 P Q H)
  · intro P
    exact total_agreement Λ ((section_constraint_laws Λ f).2.2.1 P)
  · intro P
    exact total_agreement Λ ((section_constraint_laws Λ f).2.2.2 P)

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
