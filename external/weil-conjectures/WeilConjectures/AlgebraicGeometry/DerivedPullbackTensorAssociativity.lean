/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatTensorProduct
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare


/-! # Associativity of derived pullback tensor comparisons

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-associativity).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

private theorem trifunctor_app_eq_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {H K : C ⥤ C ⥤ C ⥤ D} (a b : H ⟶ K)
    {A B C₀ A' B' C' : C} (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C₀)
    (h : ((a.app A').app B').app C' = ((b.app A').app B').app C') :
    ((a.app A).app B).app C₀ = ((b.app A).app B).app C₀ := by
  have hC : ((a.app A').app B').app C₀ = ((b.app A').app B').app C₀ := by
    rw [← cancel_epi (((H.obj A').obj B').map eC.hom)]
    rw [((a.app A').app B').naturality, ((b.app A').app B').naturality, h]
  have hB : ((a.app A').app B).app C₀ = ((b.app A').app B).app C₀ := by
    have ha := congr_app ((a.app A').naturality eB.hom) C₀
    have hb := congr_app ((b.app A').naturality eB.hom) C₀
    rw [← cancel_epi (((H.obj A').map eB.hom).app C₀)]
    change _ ≫ _ = _ ≫ _ at ha hb
    rw [ha, hb, hC]
  have ha := congr_app (congr_app (a.naturality eA.hom) B) C₀
  have hb := congr_app (congr_app (b.naturality eA.hom) B) C₀
  rw [← cancel_epi (((H.map eA.hom).app B).app C₀)]
  change _ ≫ _ = _ ≫ _ at ha hb
  rw [ha, hb, hB]

open Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem oplax_associativity_on_class
    {K₁ K₂ D₁ D₂ : Type*} [Category* K₁] [Category* K₂]
    [Category* D₁] [Category* D₂]
    [MonoidalCategory K₁] [MonoidalCategory K₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    {F : K₁ ⥤ K₂} [F.OplaxMonoidal] {G : D₁ ⥤ D₂}
    (δG : curriedTensorPost G ⟶ curriedTensorPre G)
    (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))
    (he : ∀ ⦃a b : K₁⦄ (f : a ⟶ b),
      G.map (Q₁.map f) ≫ e b = e a ≫ Q₂.map (F.map f))
    (S : K₁ → Prop)
    (hδ : ∀ a b, S a → S b →
      (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (e a ⊗ₘ e b) ≫
          μ Q₂ (F.obj a) (F.obj b) =
        G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b))
    (a b c : K₁) (ha : S a) (hb : S b) (hc : S c)
    (hab : S (a ⊗ b)) (hbc : S (b ⊗ c))
    [IsIso (e a)] [IsIso (e b)] [IsIso (e c)]
    [IsIso (μ Q₂ (F.obj a) (F.obj b))]
    [IsIso (μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c))] :
    (δG.app (Q₁.obj a ⊗ Q₁.obj b)).app (Q₁.obj c) ≫
        (δG.app (Q₁.obj a)).app (Q₁.obj b) ▷ G.obj (Q₁.obj c) ≫
          (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).hom =
      G.map (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom ≫
        (δG.app (Q₁.obj a)).app (Q₁.obj b ⊗ Q₁.obj c) ≫
          G.obj (Q₁.obj a) ◁ (δG.app (Q₁.obj b)).app (Q₁.obj c) := by
  rw [← cancel_mono ((α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).inv ≫
    ((e a ⊗ₘ e b) ⊗ₘ e c) ≫
    μ Q₂ (F.obj a) (F.obj b) ▷ Q₂.obj (F.obj c) ≫ μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c))]
  have l : ((δG.app (Q₁.obj a ⊗ Q₁.obj b)).app (Q₁.obj c) ≫
      (δG.app (Q₁.obj a)).app (Q₁.obj b) ▷ G.obj (Q₁.obj c) ≫
        (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).hom) ≫
      (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).inv ≫
        ((e a ⊗ₘ e b) ⊗ₘ e c) ≫
        μ Q₂ (F.obj a) (F.obj b) ▷ Q₂.obj (F.obj c) ≫ μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c) =
      G.map (μ Q₁ a b ▷ Q₁.obj c) ≫ G.map (μ Q₁ (a ⊗ b) c) ≫ e ((a ⊗ b) ⊗ c) ≫
        Q₂.map (δ F (a ⊗ b) c) ≫ Q₂.map (δ F a b ▷ F.obj c) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [whiskerRight_comp_tensorHom_assoc, tensorHom_comp_whiskerRight_assoc,
      Category.assoc ((δG.app (Q₁.obj a)).app (Q₁.obj b)),
      hδ a b ha hb, comp_tensorHom_comp_comp]
    simp only [Category.assoc]
    rw [μ_natural_left, app_app_comp_whiskerRight_assoc, reassoc_of% (hδ (a ⊗ b) c hab hc)]
  have r : (G.map (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom ≫
      (δG.app (Q₁.obj a)).app (Q₁.obj b ⊗ Q₁.obj c) ≫
        G.obj (Q₁.obj a) ◁ (δG.app (Q₁.obj b)).app (Q₁.obj c)) ≫
      (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).inv ≫
        ((e a ⊗ₘ e b) ⊗ₘ e c) ≫
        μ Q₂ (F.obj a) (F.obj b) ▷ Q₂.obj (F.obj c) ≫ μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c) =
      G.map (μ Q₁ a b ▷ Q₁.obj c) ≫ G.map (μ Q₁ (a ⊗ b) c) ≫ e ((a ⊗ b) ⊗ c) ≫
        Q₂.map (δ F (a ⊗ b) c) ≫ Q₂.map (δ F a b ▷ F.obj c) := by
    simp only [Category.assoc]
    rw [← associator_inv_naturality_assoc, ← Functor.LaxMonoidal.associativity_inv,
      whiskerLeft_comp_tensorHom_assoc, tensorHom_comp_whiskerLeft_assoc,
      Category.assoc ((δG.app (Q₁.obj b)).app (Q₁.obj c)), hδ b c hb hc,
      tensorHom_comp_comp_comp]
    simp only [Category.assoc]
    rw [μ_natural_right_assoc, app_app_comp_whiskerLeft_assoc, reassoc_of% (hδ a (b ⊗ c) ha hbc),
      ← G.map_comp_assoc, ← G.map_comp_assoc,
      Category.assoc (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom, ← Functor.LaxMonoidal.associativity,
      G.map_comp_assoc,
      G.map_comp_assoc]
    rw [reassoc_of% (he (α_ a b c).hom), ← Q₂.map_comp, ← Q₂.map_comp, ← Q₂.map_comp,
      Functor.OplaxMonoidal.associativity_inv, ← F.map_comp_assoc,
      Iso.hom_inv_id, F.map_id, Category.id_comp,
      Q₂.map_comp]
  rw [l, r]


private theorem tensor_associativity_of_inverse
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (G : C ⥤ D)
    (μ : curriedTensorPre G ≅ curriedTensorPost G) (A B C₀ : C)
    (h : (μ.inv.app (A ⊗ B)).app C₀ ≫
        (μ.inv.app A).app B ▷ G.obj C₀ ≫
          (α_ (G.obj A) (G.obj B) (G.obj C₀)).hom =
      G.map (α_ A B C₀).hom ≫ (μ.inv.app A).app (B ⊗ C₀) ≫
        G.obj A ◁ (μ.inv.app B).app C₀) :
    ((μ.app A).app B).hom ▷ G.obj C₀ ≫
        ((μ.app (A ⊗ B)).app C₀).hom ≫ G.map (α_ A B C₀).hom =
      (α_ (G.obj A) (G.obj B) (G.obj C₀)).hom ≫
        G.obj A ◁ ((μ.app B).app C₀).hom ≫ ((μ.app A).app (B ⊗ C₀)).hom := by
  let l := tensorIso ((μ.app A).app B) (Iso.refl (G.obj C₀)) ≪≫
    (μ.app (A ⊗ B)).app C₀ ≪≫ G.mapIso (α_ A B C₀)
  let r := (α_ (G.obj A) (G.obj B) (G.obj C₀)) ≪≫
    tensorIso (Iso.refl (G.obj A)) ((μ.app B).app C₀) ≪≫ (μ.app A).app (B ⊗ C₀)
  have hi : l.inv = r.inv := by
    dsimp [l, r]
    rw [← cancel_epi (G.map (α_ A B C₀).hom)]
    rw [← cancel_mono (α_ (G.obj A) (G.obj B) (G.obj C₀)).hom]
    simpa only [tensorIso_inv, Iso.refl_inv, tensorHom_id, id_tensorHom,
      Iso.app_inv, Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id] using h
  have hh := (Iso.inv_eq_inv l r).mp hi
  simpa only [l, r, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    Functor.mapIso_hom, tensorHom_id, id_tensorHom, Category.assoc] using hh

open Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem tensor_associativity_on_class
    {K₁ K₂ D₁ D₂ : Type*} [Category* K₁] [Category* K₂]
    [Category* D₁] [Category* D₂]
    [MonoidalCategory K₁] [MonoidalCategory K₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    {F : K₁ ⥤ K₂} [F.OplaxMonoidal] {G : D₁ ⥤ D₂}
    (m : curriedTensorPre G ≅ curriedTensorPost G)
    (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))
    (he : ∀ ⦃a b : K₁⦄ (f : a ⟶ b),
      G.map (Q₁.map f) ≫ e b = e a ≫ Q₂.map (F.map f))
    (S : K₁ → Prop)
    (hm : ∀ a b, S a → S b →
      ((m.app (Q₁.obj a)).app (Q₁.obj b)).hom ≫
          G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b) =
        (e a ⊗ₘ e b) ≫ μ Q₂ (F.obj a) (F.obj b))
    (a b c : K₁) (ha : S a) (hb : S b) (hc : S c)
    (hab : S (a ⊗ b)) (hbc : S (b ⊗ c))
    [IsIso (e a)] [IsIso (e b)] [IsIso (e c)]
    [IsIso (μ Q₂ (F.obj a) (F.obj b))]
    [IsIso (μ Q₂ (F.obj a ⊗ F.obj b) (F.obj c))] :
    ((m.app (Q₁.obj a)).app (Q₁.obj b)).hom ▷ G.obj (Q₁.obj c) ≫
        ((m.app (Q₁.obj a ⊗ Q₁.obj b)).app (Q₁.obj c)).hom ≫
          G.map (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom =
      (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).hom ≫
        G.obj (Q₁.obj a) ◁ ((m.app (Q₁.obj b)).app (Q₁.obj c)).hom ≫
          ((m.app (Q₁.obj a)).app (Q₁.obj b ⊗ Q₁.obj c)).hom := by
  apply tensor_associativity_of_inverse G m
  apply oplax_associativity_on_class m.inv e he S _ a b c ha hb hc hab hbc
  intro a b ha hb
  exact (((m.app (Q₁.obj a)).app (Q₁.obj b)).inv_comp_eq).2 (hm a b ha hb).symm

open CategoryTheory.Limits in
private theorem cochain_tensor_comparison_eq
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
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
    (F : C ⥤ D) [F.Additive] [F.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    (K L : CochainComplex C ℤ)
    (φ : (F.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj K ⊗ (F.mapHomologicalComplex (.up ℤ)).obj L)
    (hφ : ∀ p q n (h : p + q = n),
      F.map (HomologicalComplex.ιMapBifunctor K L (curriedTensor C)
          (.up ℤ) p q n h) ≫ φ.f n =
        Functor.OplaxMonoidal.δ F (K.X p) (L.X q) ≫
          HomologicalComplex.ιMapBifunctor
            ((F.mapHomologicalComplex (.up ℤ)).obj K)
            ((F.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D) (.up ℤ) p q n h) :
    φ = Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) K L := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro p q h
  rw [hφ p q n h]
  simp only [Functor.mapCochainComplex_δ,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  rw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  rfl

open CategoryTheory.Limits Functor.LaxMonoidal in
private theorem cochain_tensor_associativity_on_class
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
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
    (F : C ⥤ D) [F.Additive] [F.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    (Q₁ : CochainComplex C ℤ ⥤ D₁) (Q₂ : CochainComplex D ℤ ⥤ D₂)
    [Q₁.LaxMonoidal] [Q₂.LaxMonoidal] {G : D₁ ⥤ D₂}
    (m : curriedTensorPre G ≅ curriedTensorPost G)
    (e : ∀ K, G.obj (Q₁.obj K) ⟶ Q₂.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (he : ∀ ⦃K L : CochainComplex C ℤ⦄ (f : K ⟶ L),
      G.map (Q₁.map f) ≫ e L = e K ≫ Q₂.map ((F.mapHomologicalComplex (.up ℤ)).map f))
    (S : CochainComplex C ℤ → Prop)
    (φ : ∀ K L : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) ≅
        (F.mapHomologicalComplex (.up ℤ)).obj K ⊗ (F.mapHomologicalComplex (.up ℤ)).obj L)
    (hφ : ∀ K L p q n (h : p + q = n),
      F.map (HomologicalComplex.ιMapBifunctor K L (curriedTensor C)
          (.up ℤ) p q n h) ≫ (φ K L).hom.f n =
        Functor.OplaxMonoidal.δ F (K.X p) (L.X q) ≫
          HomologicalComplex.ιMapBifunctor
            ((F.mapHomologicalComplex (.up ℤ)).obj K)
            ((F.mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor D) (.up ℤ) p q n h)
    (hm : ∀ K L, S K → S L →
      ((m.app (Q₁.obj K)).app (Q₁.obj L)).hom ≫
          G.map (μ Q₁ K L) ≫ e (K ⊗ L) ≫ Q₂.map (φ K L).hom =
        (e K ⊗ₘ e L) ≫ μ Q₂ ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L))
    (heiso : ∀ K, S K → IsIso (e K))
    (hQiso : ∀ L K, S K →
      IsIso (μ Q₂ L ((F.mapHomologicalComplex (.up ℤ)).obj K)))
    (hS : ∀ K L, S K → S L → S (K ⊗ L))
    (a b c : CochainComplex C ℤ) (ha : S a) (hb : S b) (hc : S c) :
    ((m.app (Q₁.obj a)).app (Q₁.obj b)).hom ▷ G.obj (Q₁.obj c) ≫
        ((m.app (Q₁.obj a ⊗ Q₁.obj b)).app (Q₁.obj c)).hom ≫
          G.map (α_ (Q₁.obj a) (Q₁.obj b) (Q₁.obj c)).hom =
      (α_ (G.obj (Q₁.obj a)) (G.obj (Q₁.obj b)) (G.obj (Q₁.obj c))).hom ≫
        G.obj (Q₁.obj a) ◁ ((m.app (Q₁.obj b)).app (Q₁.obj c)).hom ≫
          ((m.app (Q₁.obj a)).app (Q₁.obj b ⊗ Q₁.obj c)).hom := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  have : IsIso (e a) := heiso a ha
  have : IsIso (e b) := heiso b hb
  have : IsIso (e c) := heiso c hc
  have : IsIso (μ Q₂ (Fc.obj a) (Fc.obj b)) := hQiso _ b hb
  have : IsIso (μ Q₂ (Fc.obj a ⊗ Fc.obj b) (Fc.obj c)) := hQiso _ c hc
  refine tensor_associativity_on_class (Q₁ := Q₁) (Q₂ := Q₂) (F := Fc) m e he S ?_
    a b c ha hb hc (hS a b ha hb) (hS b c hb hc)
  intro K L hK hL
  rw [← cochain_tensor_comparison_eq F K L (φ K L).hom (hφ K L)]
  exact hm K L hK hL

private theorem pullback_preservesKFlat {T X : Scheme.{uModel}} (g : T ⟶ X)
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) [F.Additive]
    (hFE : F = Scheme.Modules.tensorPullback g)
    (K : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hK : CochainComplex.IsKFlatTensor (R := X.sheaf) K) :
    CochainComplex.IsKFlatTensor (R := T.sheaf)
      ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  subst F
  convert CochainComplex.isKFlat_pullback g.base T.sheaf X.sheaf ⟨g.c⟩ K hK using 1
  rfl

private theorem pullback_counit_isIso {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (K : CochainComplex
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hK : CochainComplex.IsKFlatTensor (R := X.sheaf) K) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
  have hFE : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      F₀, hF₀, hmap₀, hF₀add, ε₀, hderived₀, htri, hε₀⟩ :=
    (derivedPullback_spec g)
  have hF₀E : F₀ = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF₀ (fun _ _ a ↦ hmap₀ a)
  subst F₀
  have := hε₀ K hK
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullback g).IsLeftDerivedFunctor ε W := hε
  have : (derivedPullback g).IsLeftDerivedFunctor ε₀ W := hderived₀
  let e := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε ε₀ W
  have he : e.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
      ε₀.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
    simp [e, Functor.leftDerivedNatIso]
  rw [← he]
  infer_instance

private theorem localization_tensor_isIso (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))]
    (K L : CochainComplex
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) ℤ)
    (hL : CochainComplex.IsKFlatTensor (R := S.sheaf) L) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L) := by
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, uModel, uModel} _
  let q := HomotopyCategory.quotient
    (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)
  have hk : W.kFlat (q.obj L) := by
    apply (HomotopyCategory.kFlat_iff_preserves_acyclic _).2
    intro M hM
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    have hN := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).1 hM
    have hLN := hL N hN
    constructor
    · apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
      exact hLN.of_iso (β_ L N).symm
    · exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hLN
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj K) (q.obj L)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right
      DerivedCategory.Qh W (q.obj K) (q.obj L) hk
  let e := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))
  change IsIso ((e.inv.app K ⊗ₘ e.inv.app L) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj K) (q.obj L) ≫
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ q K L)) ≫ e.hom.app (K ⊗ L))
  infer_instance

/-- Associativity on three K-flat representatives, before resolving arbitrary objects.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; parent associativity proof, steps 1 and 2.
(blueprint: lem-pc-derived-pullback-tensor-associativity).
Proof: the tensor products P tensor N and N tensor R are K-flat by 079R.
The counit epsilon is invertible on K-flat objects: identify F with tensorPullback
using hF and hmap, and compare epsilon with the counit in exists_derivedPullback
by uniqueness of left-derived functors. The localization tensorator is invertible
on K-flat pairs, including the images under F, since pullback preserves K-flatness.
Use naturality of mu to replace its components at Q(P) tensor Q(N), and at
Q(N) tensor Q(R), by components at the corresponding total tensor complexes.
Postcompose both proposed composites with L of the right-bracketed localization
comparison, then with the counit and Q of the two right-bracketed phi comparisons.
The four instances of hmu for (P,N), (P tensor N,R), (N,R), and (P,N tensor R)
replace the derived tensorators with localization tensorators and counits.
Naturality of epsilon and associativity of the lax monoidal localization Q leave
the image under Q of the associativity diagram for phi. To check that diagram,
precompose in every degree n with F of each triple total-tensor summand inclusion,
indexed by p+q+r=n. The inclusions are jointly epic, since F is the left adjoint
tensor pullback and therefore preserves their coproduct. The summand formula hphi
turns the two paths into inverse tensorators of mF; inverse monoidal associativity
at P.X p, N.X q, R.X r equates them. Coproduct extensionality and then complex
extensionality give the diagram. Apply Q and cancel the invertible comparison
maps. This proves only the representative identity; it does not transport it to
arbitrary derived objects. Zero complexes and the empty scheme require no separate
nonvanishing assumptions: the same summand and cancellation argument applies. -/
private theorem derivedPullback_tensor_associativity_kFlat {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (P N R : CochainComplex
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N)
    (hR : CochainComplex.IsKFlatTensor (R := X.sheaf) R)
    : let A := DerivedCategory.Q.obj P;
      let B := DerivedCategory.Q.obj N;
      let C := DerivedCategory.Q.obj R;
        ((μ.app A).app B).hom ▷ (derivedPullback g).obj C ≫
            ((μ.app (A ⊗ B)).app C).hom ≫ (derivedPullback g).map (α_ A B C).hom =
          (α_ ((derivedPullback g).obj A) ((derivedPullback g).obj B)
            ((derivedPullback g).obj C)).hom ≫
            (derivedPullback g).obj A ◁ ((μ.app B).app C).hom ≫
            ((μ.app A).app (B ⊗ C)).hom  := by
  let := mF.toMonoidal
  have hFE : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  have : F.IsLeftAdjoint := by
    subst F
    obtain ⟨adj, _⟩ := Scheme.Modules.exists_tensorPullbackAdjunction g
    exact ⟨_, ⟨adj⟩⟩
  exact cochain_tensor_associativity_on_class F
    (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)))
    (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings T.toRingedSpace))) μ
    (fun K ↦ ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K))
    (fun {_ _} a ↦ ε.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map a))
    (CochainComplex.IsKFlatTensor (R := X.sheaf)) φ hφ hμ
    (pullback_counit_isIso g F hF hmap ε hε)
    (fun L K hK ↦ localization_tensor_isIso T L _ (pullback_preservesKFlat g F hFE K hK))
    (fun K L hK hL ↦ CochainComplex.IsKFlatTensor.mapBifunctor K L hK hL)
    P N R hP hN hR


/-- The extended natural tensor comparison satisfies the associativity law.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; parent descent proof, step 3 (associativity).
(blueprint: lem-pc-derived-pullback-tensor-associativity).
Proof: resolve the three derived arguments by K-flat complexes P, N, and R.
Their two bracketed tensor products are K-flat. The comparison formula hμ identifies
both sides, after composition with the invertible localization tensorators and counits,
with the two termwise maps from F(P) tensor F(N) tensor F(R) to F of the triple tensor.
Precompose in each total degree with the inclusion of each summand indexed by p,q,r.
The summand formula hφ identifies each occurrence of phi with the inverse tensorator
of mF. The resulting equality is precisely associativity of mF at P.X p, N.X q,
and R.X r. Coproduct extensionality proves equality of the complex maps; applying Q
and cancelling the invertible comparison maps gives the desired identity on these
K-flat representatives. Both composites are natural in all three derived arguments
because μ is an isomorphism of bifunctors. Transport the identity along the three
resolution isomorphisms to obtain it on arbitrary objects. No unit isomorphism or
unitality law is used. -/
theorem derivedPullback_tensor_associativity {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _)))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    : ∀ A B C : schemeDerivedCategory X,
        ((μ.app A).app B).hom ▷ (derivedPullback g).obj C ≫
            ((μ.app (A ⊗ B)).app C).hom ≫ (derivedPullback g).map (α_ A B C).hom =
          (α_ ((derivedPullback g).obj A) ((derivedPullback g).obj B)
            ((derivedPullback g).obj C)).hom ≫
            (derivedPullback g).obj A ◁ ((μ.app B).app C).hom ≫
            ((μ.app A).app (B ⊗ C)).hom  := by
  intro A B C
  let Q := DerivedCategory.Q
    (C := SheafOfModules.{uModel} (moduleRings X.toRingedSpace))
  obtain ⟨P, sP, hP, _, hsP, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage A)
  obtain ⟨N, sN, hN, _, hsN, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage B)
  obtain ⟨R, sR, hR, _, hsR, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage C)
  have : QuasiIso sP := hsP
  have : QuasiIso sN := hsN
  have : QuasiIso sR := hsR
  let eA : Q.obj P ≅ A := asIso (Q.map sP) ≪≫ Q.objObjPreimageIso A
  let eB : Q.obj N ≅ B := asIso (Q.map sN) ≪≫ Q.objObjPreimageIso B
  let eC : Q.obj R ≅ C := asIso (Q.map sR) ≪≫ Q.objObjPreimageIso C
  exact trifunctor_app_eq_of_iso
    (Functor.LaxMonoidal.ofBifunctor.firstMap μ.hom)
    (Functor.LaxMonoidal.ofBifunctor.secondMap μ.hom) eA eB eC
    (derivedPullback_tensor_associativity_kFlat g F hF hmap mF ε hε φ hφ μ hμ
      P N R hP hN hR)

end AlgebraicGeometry
