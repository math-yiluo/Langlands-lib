/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
import all WeilConjectures.SecSmoothPurity.CochainInverseComparison
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Tensor transport along an isomorphism of ring sheaves

Source: Stacks Project, Modules on Sites, Section 03EK, and Cohomology on Sites,
Tags 06YN, 06YP, 06YS and 06YT
(auxiliary; not a blueprint node).

The derived clause supplies symmetric derived tensors whose
monoidal localization maps are invertible on K-flat pairs. The normalization square
uses the same total-complex comparison as the ordinary transport.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wR wS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor.OplaxMonoidal

open CategoryTheory.Category HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

private theorem cochain_braiding_delta [G.OplaxMonoidal]
    (hG : ∀ X Y : C, G.map (β_ X Y).hom ≫ δ G Y X = δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom ≫
        ((mapHomologicalComplexδNatTrans (.up ℤ) G).app L).app K =
      ((mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L ≫
        (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom := by
  ext n
  refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
  simp only [mapHomologicalComplexδNatTrans_app_app, comp_f, mapBifunctorComparison_f,
    Functor.mapHomologicalComplex_map_f]
  have h₁ := CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := L) p q n h
  have h₂ := CochainComplex.Monoidal.ι_braiding_hom (K := (G.mapHomologicalComplex (.up ℤ)).obj K)
    (L := (G.mapHomologicalComplex (.up ℤ)).obj L) p q n h
  erw [← G.map_comp_assoc, h₁, map_ιMapBifunctor_mapBifunctorComparisonX_assoc, h₂]
  rw [G.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, G.map_comp, assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX]
  simp only [mapBifunctorComparisonApp, δNatTrans_app_app]
  rw [reassoc_of% hG]
  rfl

@[instance_reducible]
private noncomputable def cochainBraided [bg : G.Braided] :
    (G.mapHomologicalComplex (.up ℤ)).Braided := by
  let := Functor.mapCochainComplexMonoidal G
  refine { toMonoidal := inferInstance, braided := ?_ }
  intro P Q
  apply (cancel_mono (Functor.OplaxMonoidal.δ
    (G.mapHomologicalComplex (.up ℤ)) Q P)).1
  have h := Functor.OplaxMonoidal.cochain_braiding_delta G
    (fun X Y ↦ by
      apply (cancel_epi (Functor.LaxMonoidal.μ G X Y)).1
      rw [← Category.assoc, Functor.LaxBraided.braided, Category.assoc,
        Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]) P Q
  simp only [← Functor.mapCochainComplex_δ] at h
  rw [Category.assoc, h, Functor.Monoidal.μ_δ_assoc, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

end CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory

private def coreOfBraidedInverse {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
    (F : A ⥤ B) (e : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (t : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (hnl : ∀ {X Y : A} (f : X ⟶ Y) Z,
      (t X Z).hom ≫ (F.map f ▷ F.obj Z) = F.map (f ▷ Z) ≫ (t Y Z).hom)
    (hnr : ∀ {X Y : A} Z (f : X ⟶ Y),
      (t Z X).hom ≫ (F.obj Z ◁ F.map f) = F.map (Z ◁ f) ≫ (t Z Y).hom)
    (ha : ∀ X Y Z,
      (t (X ⊗ Y) Z).hom ≫ ((t X Y).hom ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ (t X (Y ⊗ Z)).hom ≫ (F.obj X ◁ (t Y Z).hom))
    (hr : ∀ X, (t X (𝟙_ A)).hom ≫ (F.obj X ◁ e.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (hb : ∀ X Y, F.map (β_ X Y).hom ≫ (t Y X).hom =
      (t X Y).hom ≫ (β_ (F.obj X) (F.obj Y)).hom) : F.CoreMonoidal := by
  have hl (X : A) : F.map (λ_ X).hom = (t (𝟙_ A) X).hom ≫
      (e.hom ▷ F.obj X) ≫ (λ_ (F.obj X)).hom := by
    calc
      _ = F.map (β_ (𝟙_ A) X).hom ≫ F.map (ρ_ X).hom := by
        rw [← F.map_comp, braiding_rightUnitor]
      _ = F.map (β_ (𝟙_ A) X).hom ≫ (t X (𝟙_ A)).hom ≫
          (F.obj X ◁ e.hom) ≫ (ρ_ (F.obj X)).hom := by rw [hr]
      _ = (t (𝟙_ A) X).hom ≫ (β_ (F.obj (𝟙_ A)) (F.obj X)).hom ≫
          (F.obj X ◁ e.hom) ≫ (ρ_ (F.obj X)).hom := by
        rw [← Category.assoc, ← Category.assoc, hb, Category.assoc, Category.assoc]
      _ = _ := by
        rw [← id_tensorHom, ← tensorHom_id,
          ← BraidedCategory.braiding_naturality_assoc, braiding_rightUnitor]
  refine Functor.CoreMonoidal.mk' e.symm (fun X Y ↦ (t X Y).symm)
    hnl hnr ha ?_ ?_
  · intro X
    apply (cancel_epi (F.map (λ_ X).hom)).1
    rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
    rw [hl X, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  · intro X
    apply (cancel_epi (F.map (ρ_ X).hom)).1
    rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
    rw [← hr X, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem nativeTensorPackage {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [SymmetricCategory A] (L : A ⥤ B) (W : MorphismProperty A)
    [L.IsLocalization W] [W.ContainsIdentities] [W.RespectsIso]
    [W.HasTwoOutOfThreeProperty] [W.localizerMorphismKFlat.IsLeftDerivabilityStructure] :
    ∃ m : MonoidalCategory B, letI := m
      ∃ b : SymmetricCategory B, letI := b
        ∃ q : L.LaxBraided, letI := q
          IsIso (Functor.LaxMonoidal.ε L) ∧
            ∀ X Y, W.kFlat Y → IsIso (Functor.LaxMonoidal.μ L X Y) := by
  change ∃ m : MonoidalCategory (DerivedMonoidal L W), letI := m
    ∃ b : SymmetricCategory (DerivedMonoidal L W), letI := b
      ∃ q : (toDerivedMonoidal L W).LaxBraided, letI := q
        IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal L W)) ∧
          ∀ X Y, W.kFlat Y → IsIso (Functor.LaxMonoidal.μ (toDerivedMonoidal L W) X Y)
  let m : MonoidalCategory (DerivedMonoidal L W) :=
    DerivedMonoidal.instMonoidalCategory L W
  let b : SymmetricCategory (DerivedMonoidal L W) :=
    RingedDerivedNative.localizedSymmetric L W
  let q : (toDerivedMonoidal L W).LaxBraided :=
    { toLaxMonoidal := DerivedMonoidal.instLaxMonoidalToDerivedMonoidal L W
      braided X Y := (DerivedMonoidal.braiding_hom_μ L W X Y).symm }
  refine ⟨m, b, q, ?_, ?_⟩
  · exact inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal L W)))
  · intro X Y hY
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_right L W X Y hY

private theorem flat_obj_iff_of_monoidal_equivalence {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal] [F.IsEquivalence]
    (M : A) : ObjectProperty.flat (F.obj M) ↔ ObjectProperty.flat M := by
  let : F.PreservesFlat := F.preservesFlat_of_isEquivalence
  let : F.asEquivalence.functor.Monoidal := by
    change F.Monoidal
    infer_instance
  let : F.inv.Monoidal := F.asEquivalence.inverseMonoidal
  let : F.inv.PreservesFlat := F.inv.preservesFlat_of_isEquivalence
  constructor
  · intro h
    exact ObjectProperty.prop_of_iso _ (F.asEquivalence.unitIso.app M).symm
      (Functor.PreservesFlat.flat_obj (F := F.inv) h)
  · exact Functor.PreservesFlat.flat_obj

private theorem tensorPredicate_iff_of_equivalence {A B : Type*}
    [Category* A] [Category* B] [MonoidalCategory A] [MonoidalCategory B]
    (e : A ≌ B) [e.functor.Monoidal] (a : A → Prop) (b : B → Prop)
    (hb : ∀ {X Y : B}, (X ≅ Y) → b X → b Y)
    (hf : ∀ X, b (e.functor.obj X) ↔ a X) (P : A) :
    (∀ Y, b Y → b (Y ⊗ e.functor.obj P)) ↔
      (∀ X, a X → a (X ⊗ P)) := by
  constructor
  · intro h X hX
    exact (hf (X ⊗ P)).1
      (hb (Functor.Monoidal.μIso e.functor X P)
        (h (e.functor.obj X) ((hf X).2 hX)))
  · intro h Y hY
    let X := e.inverse.obj Y
    have hX : a X := (hf X).1 (hb (e.counitIso.app Y).symm hY)
    have h' : b (e.functor.obj (X ⊗ P)) := (hf _).2 (h X hX)
    exact hb (tensorIso (e.counitIso.app Y) (Iso.refl _))
      (hb (Functor.Monoidal.μIso e.functor X P).symm h')

private theorem cochainKFlatCriterion {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [∀ (j : ℤ), HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P : CochainComplex A ℤ) :
    (∀ Z : CochainComplex A ℤ, Z.Acyclic → (Z ⊗ P).Acyclic) ↔
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff P,
    HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)]
  constructor
  · intro hP Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z P (curriedTensor _))).2 (hP Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      ((HomotopyCategory.quotient _ _).mapIso (β_ Z P)) hr, hr⟩
  · intro hP Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hP _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).2 hZ)).2

end CategoryTheory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

local instance scalarPresheafCoproducts (A : Sheaf J CommRingCat.{r})
    (K : Type r) : HasColimitsOfShape (Discrete K)
      (PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

local instance scalarSheafCoproducts (A : Sheaf J CommRingCat.{r})
    (K : Type r) : HasColimitsOfShape (Discrete K) (scalarModules J A) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

local instance scalarSheafSmallCoproducts (A : Sheaf J CommRingCat.{r})
    (K : Type) : HasColimitsOfShape (Discrete K) (scalarModules J A) := by
  have : HasColimitsOfShape (Discrete K)
      (PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

/-- The existing monoidal structure on module cochain complexes, cached for elaboration.
Source: Stacks 03EK and 06YT
(auxiliary; not a blueprint node). -/
noncomputable instance (priority := 2000) ringIsoCochainMonoidal
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategory (CochainComplex (scalarModules J A) ℤ) :=
  HomologicalComplex.monoidalCategory (C := scalarModules J A) (c := .up ℤ)

/-- The underlying structure of the existing total tensor, cached for elaboration.
Source: Stacks 03EK and 06YT
(auxiliary; not a blueprint node). -/
noncomputable instance (priority := 2000) ringIsoCochainMonoidalStruct
    (A : Sheaf J CommRingCat.{r}) :
    MonoidalCategoryStruct (CochainComplex (scalarModules J A) ℤ) :=
  HomologicalComplex.monoidalCategoryStruct (C := scalarModules J A) (c := .up ℤ)

/-- Localization of termwise restriction, allowing independent localization universes.
Source: Stacks 04VG and 06YP
(auxiliary; not a blueprint node). -/
noncomputable def ringIsoDerivedRestriction (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    (h : exactFunctor _ _ (scalarRestriction c.hom)) :
    DerivedCategory (scalarModules J S) ⥤ DerivedCategory (scalarModules J R) :=
  letI : PreservesFiniteLimits (scalarRestriction c.hom) := h.1
  letI : PreservesFiniteColimits (scalarRestriction c.hom) := h.2
  (scalarRestriction c.hom).mapDerivedCategory

/-- The canonical localization comparison for termwise scalar restriction.
Source: Stacks 04VG and 06YP
(auxiliary; not a blueprint node). -/
noncomputable def ringIsoRestrictionComparison (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    (h : exactFunctor _ _ (scalarRestriction c.hom)) :
    DerivedCategory.Q ⋙ ringIsoDerivedRestriction c h ≅
      (scalarRestriction c.hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  letI : PreservesFiniteLimits (scalarRestriction c.hom) := h.1
  letI : PreservesFiniteColimits (scalarRestriction c.hom) := h.2
  (scalarRestriction c.hom).mapDerivedCategoryFactors

/-- The derived symmetric tensors and the representative normalization of their comparison.
The existential presentations include their localization maps, invertible on K-flat pairs
and at the unit. Thus they present the actual derived tensor, rather than impose
additional tensor hypotheses on the input categories or derived objects.
Source: Stacks 06YS, 06YT and 06YP
(auxiliary; not a blueprint node). -/
def RingIsoDerivedTensorCompatible
    (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    (h : exactFunctor _ _ (scalarRestriction c.hom))
    (t : ∀ P Q : CochainComplex (scalarModules J S) ℤ,
      ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P ⊗
          ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) : Prop :=
  ∃ (mR : MonoidalCategory (DerivedCategory (scalarModules J R)))
    (mS : MonoidalCategory (DerivedCategory (scalarModules J S))),
    letI := mR
    letI := mS
    ∃ (bR : SymmetricCategory (DerivedCategory (scalarModules J R)))
      (bS : SymmetricCategory (DerivedCategory (scalarModules J S))),
      letI := bR
      letI := bS
      ∃ (qR : (DerivedCategory.Q (C := scalarModules J R)).LaxBraided)
        (qS : (DerivedCategory.Q (C := scalarModules J S)).LaxBraided),
        letI := qR
        letI := qS
        IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := scalarModules J R))) ∧
        IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := scalarModules J S))) ∧
        (∀ P Q : CochainComplex (scalarModules J R) ℤ,
          P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
            IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ∧
        (∀ P Q : CochainComplex (scalarModules J S) ℤ,
          P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
            IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ∧
        ∃ d : (ringIsoDerivedRestriction c h).Braided,
          ∀ (P Q : CochainComplex (scalarModules J S) ℤ),
            P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
            d.toMonoidal.toOplaxMonoidal.δ
                (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
              ((ringIsoRestrictionComparison c h).hom.app P ⊗ₘ
                (ringIsoRestrictionComparison c h).hom.app Q) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P)
                (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) =
            (ringIsoDerivedRestriction c h).map
                (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
              (ringIsoRestrictionComparison c h).hom.app (P ⊗ Q) ≫
              DerivedCategory.Q.map (t P Q).hom

/-- All clauses of scalar-coordinate tensor transport, with the tensor and unit maps
normalized on sections and the total-complex map normalized on every summand.
Source: Stacks 03EK, 06YN and 06YP
(auxiliary; not a blueprint node). -/
structure RingIsoTensorTransport (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)] where
  /-- The ordinary equivalence is the given restriction in both directions. -/
  equivalence : scalarModules J S ≌ scalarModules J R
  functor_eq : equivalence.functor = scalarRestriction c.hom
  inverse_eq : equivalence.inverse = scalarRestriction c.inv
  /-- Restriction is additive and exact. -/
  additive : (scalarRestriction c.hom).Additive
  exact : exactFunctor _ _ (scalarRestriction c.hom)
  /-- Strong symmetric tensor coherence, including associators and both unitors. -/
  monoidal : (scalarRestriction c.hom).Braided
  /-- The forward tensor map is the identity on local pure tensors. -/
  pure_hom : ∀ (M N : scalarModules J S) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U),
    (monoidal.toMonoidal.toOplaxMonoidal.δ M N).val.app U
        (ScalarHomOrdinary.pure S M N U x y) =
      ScalarHomOrdinary.pure R ((scalarRestriction c.hom).obj M)
        ((scalarRestriction c.hom).obj N) U x y
  /-- The inverse tensor map has exactly the same generator formula. -/
  pure_inv : ∀ (M N : scalarModules J S) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U),
    (monoidal.toMonoidal.toLaxMonoidal.μ M N).val.app U
        (ScalarHomOrdinary.pure R ((scalarRestriction c.hom).obj M)
          ((scalarRestriction c.hom).obj N) U x y) =
      ScalarHomOrdinary.pure S M N U x y
  /-- On the regular module the unit map is the inverse ring-sheaf isomorphism. -/
  unit_hom : ∀ (U : Cᵒᵖ) (s : S.obj.obj U),
    monoidal.toMonoidal.toOplaxMonoidal.η.val.app U s = c.inv.hom.app U s
  /-- Termwise restriction identifies the actual direct-sum total tensor complexes. -/
  totalIso : ∀ P Q : CochainComplex (scalarModules J S) ℤ,
    ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q
  /-- Naturality in both complex variables. -/
  total_naturality : ∀ {P P' Q Q' : CochainComplex (scalarModules J S) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q'),
    ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).map (f ⊗ₘ g) ≫
        (totalIso P' Q').hom =
      (totalIso P Q).hom ≫
        (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
          ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).map g)
  /-- Its degree-n summand is precisely the ordinary tensor map. -/
  total_summand : ∀ (P Q : CochainComplex (scalarModules J S) ℤ)
    (p q n : ℤ) (h : p + q = n),
    (scalarRestriction c.hom).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        ((totalIso P Q).hom.f n) =
      monoidal.toMonoidal.toOplaxMonoidal.δ (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P)
          (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) p q n h
  /-- Preservation and reflection of acyclicity, without boundedness assumptions. -/
  acyclic_iff : ∀ P : CochainComplex (scalarModules J S) ℤ,
    (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔ P.Acyclic
  /-- Preservation and reflection of sheaf flatness. -/
  flat_iff : ∀ M : scalarModules J S,
    IsFlatOnSite (R := R) ((scalarRestriction c.hom).obj M) ↔ IsFlatOnSite (R := S) M
  /-- Preservation and reflection of the acyclic-tensor definition of K-flatness. -/
  kflat_iff : ∀ P : CochainComplex (scalarModules J S) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
      (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P) ↔
        P.IsKFlatIndependentCoefficients
  /-- On R-complexes the two definitions of K-flatness agree. -/
  kflat_test_R : ∀ P : CochainComplex (scalarModules J R) ℤ,
    P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor
  /-- On S-complexes the same equivalence includes both tensor orders. -/
  kflat_test_S : ∀ P : CochainComplex (scalarModules J S) ℤ,
    P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor
  /-- The coherent derived comparison is computed by this same total tensor map. -/
  derived : RingIsoDerivedTensorCompatible c exact totalIso

noncomputable section

set_option synthInstance.maxSize 256

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private noncomputable def scalarIsoEquivalence (c : R ≅ S) :
    scalarModules J S ≌ scalarModules J R := by
  let d := (sheafCompose J (forget₂ CommRingCat RingCat)).mapIso c
  have : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  exact pushforwardPushforwardEquivalence (CategoryTheory.Equivalence.refl (C := C)) d.hom d.inv
    (by
      change Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ))
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj =
          d.inv.hom ≫ d.hom.hom
      rw [Functor.whiskerRight_id']
      exact (congrArg (fun f ↦ f.hom) d.inv_hom_id).symm)
    (by
      change d.hom.hom ≫ d.inv.hom ≫ Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ))
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj = 𝟙 _
      rw [Functor.whiskerRight_id']
      change d.hom.hom ≫ d.inv.hom ≫
        𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj = 𝟙 _
      rw [Category.comp_id]
      exact congrArg (fun f ↦ f.hom) d.hom_inv_id)

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarRestriction_isEquivalence (c : R ≅ S) :
    (scalarRestriction c.hom).IsEquivalence :=
  (scalarIsoEquivalence c).isEquivalence_functor

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarIso_exact (c : R ≅ S) :
    exactFunctor _ _ (scalarRestriction c.hom) := by
  let : (scalarRestriction c.hom).IsEquivalence :=
    scalarRestriction_isEquivalence c
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem scalar_inv_hom (c : R ≅ S) (U : Cᵒᵖ) (r : R.obj.obj U) :
    c.inv.hom.app U (c.hom.hom.app U r) = r :=
  ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) c.hom_inv_id) r

attribute [local irreducible] monoidalCategory
attribute [local irreducible] CategoryTheory.CochainPullback.extensionFunctor
  CategoryTheory.CochainPullback.extensionComparison

open CategoryTheory.CochainPullback in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarExtensionCore_exists (a : R ⟶ S) :
    ∃ core : (extensionFunctor a).CoreMonoidal,
      (∀ M N, (core.μIso M N).inv = ((extensionComparison a).mu M N).hom) ∧
      core.εIso.inv = (moduleUnit (extensionPullback a) (extensionComparison a)).hom := by
  let f := extensionPullback a
  let k := extensionComparison a
  let core := CategoryTheory.coreOfBraidedInverse f.L (moduleUnit f k) k.mu
    (fun b N ↦ by
      simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using
        (k.naturality b (𝟙 N)).symm)
    (fun M b ↦ by
      simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using
        (k.naturality (𝟙 M) b).symm)
    (fun M N H ↦ by
      simpa only [tensorHom_id, id_tensorHom] using cochainModuleTensorAssociativity f k M N H)
    (fun M ↦ by
      simpa only [id_tensorHom] using module_right_unit f k M)
    (cochainModuleTensorBraiding f k)
  exact ⟨core, fun _ _ ↦ rfl, rfl⟩

open CategoryTheory.CochainPullback in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarExtensionBraided_exists (a : R ⟶ S) :
    ∃ b : (extensionFunctor a).Braided,
      (∀ M N, b.toMonoidal.toOplaxMonoidal.δ M N =
        ((extensionComparison a).mu M N).hom) ∧
      b.toMonoidal.toOplaxMonoidal.η =
        (moduleUnit (extensionPullback a) (extensionComparison a)).hom := by
  let f := extensionPullback a
  let k := extensionComparison a
  obtain ⟨core, hc, hu⟩ := scalarExtensionCore_exists a
  let : f.L.Monoidal := core.toMonoidal
  have hd (M N : Modules R) : Functor.OplaxMonoidal.δ f.L M N = (k.mu M N).hom := hc M N
  let b : f.L.Braided :=
    { toMonoidal := inferInstance
      braided M N := by
        apply (cancel_mono (Functor.OplaxMonoidal.δ f.L N M)).1
        rw [Category.assoc, hd, cochainModuleTensorBraiding, ← hd]
        simp only [← hd, Functor.Monoidal.μ_δ_assoc]
        rw [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id] }
  exact ⟨b, hd, hu⟩

open CategoryTheory.CochainPullback in
private noncomputable def scalarExtensionRestrictionIso (c : R ≅ S) :
    extensionFunctor c.inv ≅ scalarRestriction c.hom :=
  Adjunction.leftAdjointUniq (extensionAdjunction c.inv) (scalarIsoEquivalence c).toAdjunction

open CategoryTheory.CochainPullback in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarExtensionRestrictionIso_insertion (c : R ≅ S)
    (M : scalarModules J S) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((scalarExtensionRestrictionIso c).hom.app M).val.app U
      (extensionTmul c.inv M U 1 x) = x := by
  have h := congrArg (fun f ↦ f.val.app U x)
    (Adjunction.unit_leftAdjointUniq_hom_app (extensionAdjunction c.inv)
      (scalarIsoEquivalence c).toAdjunction M)
  have hu : ((extensionAdjunction c.inv).unit.app M).val.app U x =
      extensionTmul c.inv M U 1 x :=
    (Classical.choose_spec (extensionAdjunction_existsUnique c.inv)).1 M U x
  change ((scalarExtensionRestrictionIso c).hom.app M).val.app U
    (((extensionAdjunction c.inv).unit.app M).val.app U x) = _ at h
  erw [hu] at h
  exact h.trans (by
    change M.val.map (𝟙 U) x = x
    exact ConcreteCategory.congr_hom (M.val.presheaf.map_id U) x)

open CategoryTheory.CochainPullback in
omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarExtensionRestrictionIso_inverse (c : R ≅ S)
    (M : scalarModules J S) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((scalarExtensionRestrictionIso c).inv.app M).val.app U x =
      extensionTmul c.inv M U 1 x := by
  have h := congrArg (((scalarExtensionRestrictionIso c).inv.app M).val.app U)
    (scalarExtensionRestrictionIso_insertion c M U x)
  have hi := congrArg (fun f ↦ f.val.app U (extensionTmul c.inv M U 1 x))
    ((scalarExtensionRestrictionIso c).hom_inv_id_app M)
  exact h.symm.trans hi

attribute [local irreducible] scalarExtensionRestrictionIso

section
attribute [local semireducible] CategoryTheory.CochainPullback.extensionFunctor

open CategoryTheory.CochainPullback in
private theorem scalarExtension_tensor_pure (a : R ⟶ S) (M N : scalarModules J R)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((extensionComparison a).mu M N).hom.val.app U
      (extensionTmul a (M ⊗ N) U 1 (ScalarHomOrdinary.pure R M N U x y)) =
    ScalarHomOrdinary.pure S _ _ U (extensionTmul a M U 1 x)
      (extensionTmul a N U 1 y) := by
  let f := extensionPullback a
  let k := extensionComparison a
  let ev := sheafToPresheaf J (Type r) ⋙ (CategoryTheory.evaluation Cᵒᵖ (Type r)).obj U
  have (K : Type) : HasLimitsOfShape (Discrete K) (Type r) := Types.hasLimitsOfShape
  have (K : Type) : HasLimitsOfShape (Discrete K) (Cᵒᵖ ⥤ Type r) :=
    functorCategoryHasLimitsOfShape
  have (K : Type) : HasLimitsOfShape (Discrete K) (Sheaf J (Type r)) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J (Type r))
  obtain ⟨t, hx, hy⟩ := SheafOfModules.CochainTensorComparison.productElements ev
    ((underlying R).obj M) ((underlying R).obj N) x y
  let px : (underlying R).obj M ⨯ (underlying R).obj N ⟶ (underlying R).obj M := prod.fst
  let py : (underlying R).obj M ⨯ (underlying R).obj N ⟶ (underlying R).obj N := prod.snd
  have h := congrArg (fun q ↦ q.hom.app U t) (generator_tensorPair f k px py)
  change (k.mu M N).hom.val.app U
    ((k.q (M ⊗ N)).hom.app U
      (moduleTmul M N U (px.hom.app U t) (py.hom.app U t))) =
    moduleTmul (f.L.obj M) (f.L.obj N) U
      ((k.q M).hom.app U (px.hom.app U t))
      ((k.q N).hom.app U (py.hom.app U t)) at h
  change px.hom.app U t = x at hx
  change py.hom.app U t = y at hy
  rw [hx, hy] at h
  erw [k.q_one, k.q_one, k.q_one] at h
  exact h

end

open CategoryTheory.CochainPullback in
private theorem scalarRestriction_braided (c : R ≅ S) :
    ∃ b : (scalarRestriction c.hom).Braided,
      (∀ (M N : scalarModules J S) U x y,
        (b.toMonoidal.toOplaxMonoidal.δ M N).val.app U
          (ScalarHomOrdinary.pure S M N U x y) = ScalarHomOrdinary.pure R _ _ U x y) := by
  obtain ⟨b, hb, _⟩ := scalarExtensionBraided_exists c.inv
  let := b
  let e := scalarExtensionRestrictionIso c
  let : (scalarRestriction c.hom).Monoidal := Functor.Monoidal.transport e
  have hm : NatTrans.IsMonoidal e.hom := Functor.Monoidal.natTransIsMonoidal_of_transport e
  let lb : (scalarRestriction c.hom).LaxBraided := Functor.LaxBraided.ofNatIso e
  refine ⟨{ toMonoidal := inferInstance, braided := lb.braided }, ?_⟩
  intro M N U x y
  rw [Functor.Monoidal.transport_δ]
  change ((e.hom.app M ⊗ₘ e.hom.app N).val.app U)
    ((Functor.OplaxMonoidal.δ (extensionFunctor c.inv) M N).val.app U
      ((e.inv.app (M ⊗ N)).val.app U (ScalarHomOrdinary.pure S M N U x y))) = _
  rw [scalarExtensionRestrictionIso_inverse, hb]
  erw [scalarExtension_tensor_pure c.inv M N U x y]
  erw [CochainScalarConstruction.pure_map R (e.hom.app M) (e.hom.app N)]
  rw [scalarExtensionRestrictionIso_insertion, scalarExtensionRestrictionIso_insertion]
  rfl

omit [EssentiallySmall.{r} C] in
private theorem scalarIso_acyclic (c : R ≅ S)
    (P : CochainComplex (scalarModules J S) ℤ) :
    (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔
      P.Acyclic := by
  let F := scalarRestriction c.hom
  let : F.IsEquivalence := scalarRestriction_isEquivalence c
  constructor
  · intro h i
    exact ((P.sc i).exact_map_iff_of_faithful F).1 (h i)
  · intro h i
    exact ((P.sc i).exact_map_iff_of_faithful F).2 (h i)

@[instance_reducible]
private def scalarCochainSymmetric (A : Sheaf J CommRingCat.{r}) :
    SymmetricCategory (CochainComplex (scalarModules J A) ℤ) :=
  { toBraidedCategory := inferInstance
    symmetry := RingedDerivedNative.complex_symmetry }

section

private theorem scalar_kflat_test (A : Sheaf J CommRingCat.{r})
    (P : CochainComplex (scalarModules J A) ℤ) :
    P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor := by
  change (∀ Z : CochainComplex (scalarModules J A) ℤ, Z.Acyclic → (Z ⊗ P).Acyclic) ↔
    (HomologicalComplex.quasiIso (scalarModules J A) (.up ℤ)).kFlat P
  exact CategoryTheory.cochainKFlatCriterion P

end

private theorem scalarRestriction_pure_inv (c : R ≅ S)
    (b : (scalarRestriction c.hom).Braided)
    (hb : ∀ (M N : scalarModules J S) U x y,
      (b.toMonoidal.toOplaxMonoidal.δ M N).val.app U
        (ScalarHomOrdinary.pure S M N U x y) = ScalarHomOrdinary.pure R _ _ U x y)
    (M N : scalarModules J S) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (b.toMonoidal.toLaxMonoidal.μ M N).val.app U
      (ScalarHomOrdinary.pure R _ _ U x y) = ScalarHomOrdinary.pure S M N U x y := by
  let := b
  rw [← hb M N U x y]
  exact congrArg (fun f ↦ f.val.app U (ScalarHomOrdinary.pure S M N U x y))
    (Functor.Monoidal.δ_μ (scalarRestriction c.hom) M N)

private def scalarPureNormalized (c : R ≅ S) (b : (scalarRestriction c.hom).Braided) : Prop :=
  ∀ (M N : scalarModules J S) U x y,
    (b.toMonoidal.toOplaxMonoidal.δ M N).val.app U
      (ScalarHomOrdinary.pure S M N U x y) = ScalarHomOrdinary.pure R _ _ U x y

section
attribute [local semireducible] monoidalCategory

private theorem scalarRestriction_unit (c : R ≅ S)
    (b : (scalarRestriction c.hom).Braided)
    (hb : scalarPureNormalized c b)
    (U : Cᵒᵖ) (s : S.obj.obj U) :
    b.toMonoidal.toOplaxMonoidal.η.val.app U s = c.inv.hom.app U s := by
  let F := scalarRestriction c.hom
  let := b
  let MS : scalarModules J S := unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  let eta := Functor.OplaxMonoidal.η F
  have hp := hb MS MS U (1 : S.obj.obj U) s
  have ht := CochainScalarConstruction.pure_map R (𝟙 (F.obj MS)) eta U
    (show (F.obj MS).val.obj U from (1 : S.obj.obj U)) s
  have huR := CochainTensorComparison.UnitConstruction.unitor_pure R (F.obj MS) U
    (show (F.obj MS).val.obj U from (1 : S.obj.obj U))
    (show R.obj.obj U from eta.val.app U s)
  have huS := CochainTensorComparison.UnitConstruction.unitor_pure S MS U
    (1 : S.obj.obj U) s
  have hc := congrArg (fun f ↦ f.val.app U (ScalarHomOrdinary.pure S MS MS U (1 : S.obj.obj U) s))
    (Functor.OplaxMonoidal.right_unitality_hom F MS)
  rw [← id_tensorHom] at hc
  have h : c.hom.hom.app U (eta.val.app U s) * 1 = s * 1 :=
    huR.symm.trans ((congrArg ((ρ_ (F.obj MS)).hom.val.app U) ht.symm).trans
      ((congrArg (fun z ↦ (ρ_ (F.obj MS)).hom.val.app U
        ((𝟙 (F.obj MS) ⊗ₘ eta).val.app U z)) hp.symm).trans (hc.trans huS)))
  simp only [mul_one] at h
  have h' := congrArg (c.inv.hom.app U) h
  exact (scalar_inv_hom c U (show R.obj.obj U from eta.val.app U s)).symm.trans h'

end

private def scalarTotalIso (c : R ≅ S) [b : (scalarRestriction c.hom).Braided]
    [(scalarRestriction c.hom).IsEquivalence]
    (P Q : CochainComplex (scalarModules J S) ℤ) :
    ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q :=
  ((scalarRestriction c.hom).mapCochainComplexμIso P Q).symm

private theorem scalarRestriction_total_summand (c : R ≅ S)
    [b : (scalarRestriction c.hom).Braided]
    [(scalarRestriction c.hom).IsEquivalence]
    (P Q : CochainComplex (scalarModules J S) ℤ) (p q n : ℤ) (h : p + q = n) :
    (scalarRestriction c.hom).map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        ((scalarRestriction c.hom).mapCochainComplexμIso P Q).inv.f n =
      Functor.OplaxMonoidal.δ (scalarRestriction c.hom) (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P)
          (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  let F := scalarRestriction c.hom
  let : F.IsEquivalence := scalarRestriction_isEquivalence c
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P Q p q n h

private theorem scalarRestriction_flat (c : R ≅ S)
    [b : (scalarRestriction c.hom).Braided] (M : scalarModules J S) :
    IsFlatOnSite (R := R) ((scalarRestriction c.hom).obj M) ↔
      IsFlatOnSite (R := S) M := by
  let F := scalarRestriction c.hom
  let : F.IsEquivalence := scalarRestriction_isEquivalence c
  have ht := CategoryTheory.flat_obj_iff_of_monoidal_equivalence F M
  constructor
  · intro h
    have hM := ht.1 (flat_to_cat R _ h)
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso S M).symm hM.2
  · intro h
    have hM := ht.2 (flat_to_cat S _ h)
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (F.obj M)).symm hM.2

private theorem scalarRestriction_kflat (c : R ≅ S)
    [b : (scalarRestriction c.hom).Braided]
    (P : CochainComplex (scalarModules J S) ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P) ↔
        P.IsKFlatIndependentCoefficients := by
  let F := scalarRestriction c.hom
  let : F.IsEquivalence := scalarRestriction_isEquivalence c
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let e := F.asEquivalence.mapHomologicalComplex (.up ℤ)
  let : e.functor.Monoidal := Functor.mapCochainComplexMonoidal F
  change (∀ A : CochainComplex (scalarModules J R) ℤ,
    A.Acyclic → (A ⊗ Fc.obj P).Acyclic) ↔
      (∀ A : CochainComplex (scalarModules J S) ℤ, A.Acyclic → (A ⊗ P).Acyclic)
  exact CategoryTheory.tensorPredicate_iff_of_equivalence e
    HomologicalComplex.Acyclic HomologicalComplex.Acyclic
    (fun i h n ↦ (h n).of_iso i) (scalarIso_acyclic c) P

private theorem scalarRestriction_native_kflat (c : R ≅ S)
    [b : (scalarRestriction c.hom).Braided]
    (P : CochainComplex (scalarModules J S) ℤ)
    (hP : (HomologicalComplex.quasiIso (scalarModules J S) (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso (scalarModules J R) (.up ℤ)).kFlat
      (((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact (scalar_kflat_test R _).1
    ((scalarRestriction_kflat c P).2 ((scalar_kflat_test S P).2 hP))

private theorem scalarDerivability (A : Sheaf J CommRingCat.{r}) :
    LocalizerMorphism.IsLeftDerivabilityStructure
      (HomologicalComplex.quasiIso (scalarModules J A) (.up ℤ)).localizerMorphismKFlat := by
  have (M : scalarModules J A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients A M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : scalarModules J A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  let := hasFunctorialFlatResolution_kfi A
  have := hasExactColimits_int_kfi A
  infer_instance

@[instance_reducible]
private noncomputable def scalarComplexBraided (c : R ≅ S)
    [b : (scalarRestriction c.hom).Braided]
    [(scalarRestriction c.hom).IsEquivalence] :
    ((scalarRestriction c.hom).mapHomologicalComplex (.up ℤ)).Braided := by
  exact Functor.OplaxMonoidal.cochainBraided (scalarRestriction c.hom)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarRestriction_derived (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)]
    [b : (scalarRestriction c.hom).Braided]
    [(scalarRestriction c.hom).IsEquivalence] :
    RingIsoDerivedTensorCompatible c (scalarIso_exact c)
      (scalarTotalIso c) := by
  unfold RingIsoDerivedTensorCompatible
  let F := scalarRestriction c.hom
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let G := ringIsoDerivedRestriction c (scalarIso_exact c)
  let QR : CochainComplex (scalarModules J R) ℤ ⥤ DerivedCategory (scalarModules J R) :=
    DerivedCategory.Q
  let QS : CochainComplex (scalarModules J S) ℤ ⥤ DerivedCategory (scalarModules J S) :=
    DerivedCategory.Q
  let WR := HomologicalComplex.quasiIso (scalarModules J R) (.up ℤ)
  let WS := HomologicalComplex.quasiIso (scalarModules J S) (.up ℤ)
  let : WR.localizerMorphismKFlat.IsLeftDerivabilityStructure := scalarDerivability R
  let : WS.localizerMorphismKFlat.IsLeftDerivabilityStructure := scalarDerivability S
  let := scalarCochainSymmetric R
  let := scalarCochainSymmetric S
  obtain ⟨mR, bR, qR, hεR, hμR⟩ := CategoryTheory.nativeTensorPackage QR WR
  obtain ⟨mS, bS, qS, hεS, hμS⟩ := CategoryTheory.nativeTensorPackage QS WS
  let := mR
  let := mS
  let := bR
  let := bS
  let := qR
  let := qS
  have hFP (P : CochainComplex (scalarModules J S) ℤ) (hP : WS.kFlat P) :
      WR.kFlat (Fc.obj P) :=
    scalarRestriction_native_kflat c P hP
  let : Fc.Braided := scalarComplexBraided c
  obtain ⟨d, hd⟩ := braidedLocalizationSquare QS QR Fc G
    (ringIsoRestrictionComparison c (scalarIso_exact c)) WS (fun X ↦ by
      let K := QS.objPreimage X
      obtain ⟨P, f, hP, _, hf, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
      exact ⟨P, (scalar_kflat_test S P).1 hP,
        ⟨Localization.isoOfHom QS WS f hf ≪≫ QS.objObjPreimageIso X⟩⟩)
    hμS (fun X P hP ↦ hμR X (Fc.obj P) (hFP P hP))
  refine ⟨mR, mS, bR, bS, qR, qS, hεR, hεS, ?_, ?_, d, ?_⟩
  · intro P Q _ hQ
    exact hμR P Q ((scalar_kflat_test R Q).1 hQ)
  · intro P Q _ hQ
    exact hμS P Q ((scalar_kflat_test S Q).1 hQ)
  · intro P Q _ _
    exact hd P Q

/-- Restriction along a ring-sheaf isomorphism transports tensor, flatness and K-flatness,
and its unbounded derived extension has the coherent normalized tensor comparison.
Source: Stacks 03EK, 03CY, 06YN, 06YP, 06YS and 06YT
(auxiliary; not a blueprint node).

Proof:
1. Restrict back along the inverse. Both composites are identity on abelian sheaves;
   the scalar actions agree by c inverse c = id. This gives the additive exact equivalence.
2. On section tensors send x tensor y to x tensor y in both directions. Surjectivity
   of c makes the S-balanced relation R-balanced. Sheafification extends these maps
   uniquely. The unit is c inverse. On pure tensors the associator, unitor and symmetry
   diagrams commute, hence they commute on the sheafified tensor.
3. Sum the comparisons in each degree over p+q=n. Naturality commutes with both
   differential terms; additivity preserves the sign (-1)^p. This yields totalIso.
4. Exactness identifies cohomology; the inverse equivalence reflects zero objects.
   Tensor the inverse image of a short exact sequence to transport flatness.
5. For any acyclic R-complex A, its inverse image is acyclic. Tensor it with the
   S-K-flat P and transport the total tensor back. Interchange c and its inverse
   to obtain reflection and the corresponding assertion for the inverse functor.
6. Tensor commutes with mapping cones. The acyclic-cone criterion proves that the
   acyclic-tensor test preserves quasi-isomorphisms on either side (06YP), using
   signed symmetry for the other order. Conversely apply tensor to zero -> A.
7. Localize the exact termwise equivalence. K-flat resolutions correspond by steps
   4-5, and step 3 gives the derived comparison on them. The resolving-subcategory
   descent theorem extends it uniquely and naturally to all derived pairs.
8. Check derived coherence on three K-flat resolutions, whose pairwise tensors are
   K-flat. The diagrams are those of step 2 summed over triple degrees; symmetry
   includes (-1)^(pq). Faithfulness of restriction to resolutions proves coherence
   for all derived objects. The displayed derived square records the computation
   on every corresponding pair of K-flat resolutions, independently of choices. -/
theorem ringIso_tensor_transport (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)] :
    Nonempty (RingIsoTensorTransport c) := by
  let F := scalarRestriction c.hom
  let : F.IsEquivalence := scalarRestriction_isEquivalence c
  obtain ⟨b, hb⟩ := scalarRestriction_braided c
  let := b
  let := Functor.mapCochainComplexMonoidal F
  refine ⟨{
    equivalence := scalarIsoEquivalence c
    functor_eq := rfl
    inverse_eq := rfl
    additive := inferInstance
    exact := scalarIso_exact c
    monoidal := b
    pure_hom := hb
    pure_inv := scalarRestriction_pure_inv c b hb
    unit_hom := scalarRestriction_unit c b hb
    totalIso := scalarTotalIso c
    total_naturality := ?_
    total_summand := scalarRestriction_total_summand c
    acyclic_iff := scalarIso_acyclic c
    flat_iff := scalarRestriction_flat c
    kflat_iff := scalarRestriction_kflat c
    kflat_test_R := scalar_kflat_test R
    kflat_test_S := scalar_kflat_test S
    derived := scalarRestriction_derived c }⟩
  intro P P' Q Q' f g
  exact (Functor.OplaxMonoidal.δ_natural
    (F.mapHomologicalComplex (.up ℤ)) f g).symm

end

end SheafOfModules
