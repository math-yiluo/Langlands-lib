/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelOrdinaryScalar
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Ordinary quotient extension of a free model complex

Source: blueprint latest, integral ctf-equals-bc, Local models; Stacks 093M and 0G7E.
(blueprint: lem-sfb-finite-model-ordinary-free-complex). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def sumComparison {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] (X : C) (n : ℕ) :
    F.obj (⨁ fun _ : Fin n ↦ X) ≅ ⨁ fun _ : Fin n ↦ F.obj X :=
  F.mapBiproduct _

private lemma matrix_square {C D Z : Type*} [Category* C] [Category* D] [Category* Z]
    [Preadditive C] [Preadditive D] [Preadditive Z]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts Z]
    (F : C ⥤ Z) (G : D ⥤ Z) [F.Additive] [G.Additive]
    {X : C} {Y : D} (e : F.obj X ≅ G.obj Y) (a b : ℕ)
    (v : Fin a → Fin b → (X ⟶ X)) (w : Fin a → Fin b → (Y ⟶ Y))
    (h : ∀ j i, F.map (v j i) ≫ e.hom = e.hom ≫ G.map (w j i)) :
    F.map (biproduct.matrix v) ≫
        ((sumComparison F X b) ≪≫ biproduct.mapIso (fun _ ↦ e) ≪≫
          (sumComparison G Y b).symm).hom =
      ((sumComparison F X a) ≪≫ biproduct.mapIso (fun _ ↦ e) ≪≫
        (sumComparison G Y a).symm).hom ≫ G.map (biproduct.matrix w) := by
  apply (cancel_mono (sumComparison G Y b).hom).mp
  apply (cancel_epi (sumComparison F X a).inv).mp
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  have hι (r : ℕ) (k : Fin r) :
      biproduct.ι (fun _ : Fin r ↦ F.obj X) k ≫ (sumComparison F X r).inv =
        F.map (biproduct.ι (fun _ : Fin r ↦ X) k) := by
    change _ ≫ biproduct.desc (fun j ↦ F.map (biproduct.ι _ j)) = _
    exact biproduct.ι_desc _ _
  have hπ (r : ℕ) (k : Fin r) :
      (sumComparison G Y r).hom ≫ biproduct.π (fun _ : Fin r ↦ G.obj Y) k =
        G.map (biproduct.π (fun _ : Fin r ↦ Y) k) := by
    change biproduct.lift (fun j ↦ G.map (biproduct.π _ j)) ≫ _ = _
    exact biproduct.lift_π _ _
  have hπF (r : ℕ) (k : Fin r) :
      (sumComparison F X r).hom ≫ biproduct.π (fun _ : Fin r ↦ F.obj X) k =
        F.map (biproduct.π (fun _ : Fin r ↦ X) k) := by
    change biproduct.lift (fun j ↦ F.map (biproduct.π _ j)) ≫ _ = _
    exact biproduct.lift_π _ _
  have hιG (r : ℕ) (k : Fin r) :
      biproduct.ι (fun _ : Fin r ↦ G.obj Y) k ≫ (sumComparison G Y r).inv =
        G.map (biproduct.ι (fun _ : Fin r ↦ Y) k) := by
    change _ ≫ biproduct.desc (fun j ↦ G.map (biproduct.ι _ j)) = _
    exact biproduct.ι_desc _ _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    biproduct.mapIso_hom, biproduct.map_π, biproduct.ι_map_assoc]
  rw [← Category.assoc (biproduct.ι _ j) (sumComparison F X a).inv, hι]
  rw [← Category.assoc (sumComparison F X b).hom, hπF]
  rw [← Category.assoc (biproduct.ι _ j) (sumComparison G Y a).inv, hιG]
  rw [hπ, ← F.map_comp_assoc, ← F.map_comp_assoc, ← G.map_comp, ← G.map_comp]
  simpa only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.lift_π] using h j i

private lemma integral_matrix (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    (ModuleCat.biproductIsoPi
        (fun _ : Fin a ↦ ModuleCat.of (A l E) (ULift.{u + 1} (A l E)))).hom ≫
      integralDifferential l E a b v ≫
      (ModuleCat.biproductIsoPi
        (fun _ : Fin b ↦ ModuleCat.of (A l E) (ULift.{u + 1} (A l E)))).inv =
    biproduct.matrix (fun j i ↦ ModuleCat.ofHom
      (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) (v i j))) := by
  classical
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, ModuleCat.biproductIsoPi_inv_comp_π,
    biproduct.ι_matrix_assoc, biproduct.lift_π]
  have hι : biproduct.ι
      (fun _ : Fin a ↦ ModuleCat.of (A l E) (ULift.{u + 1} (A l E))) j ≫
      (ModuleCat.biproductIsoPi _).hom =
      ModuleCat.ofHom (LinearMap.single (A l E) (fun _ : Fin a ↦ ULift.{u + 1} (A l E)) j) := by
    apply (cancel_mono (ModuleCat.biproductIsoPi _).inv).mp
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [ModuleCat.biproductIsoPi_inv_comp_π]
    rw [biproduct.ι_π]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only []
    split_ifs <;> simp_all
  rw [← Category.assoc, ← Category.assoc, hι]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ULift.up (∑ k : Fin a, v i k *
    ((Pi.single j x : Fin a → ULift.{u + 1} (A l E)) k).down) =
      ULift.up (v i j * x.down)
  simp [Pi.single_apply, apply_ite, mul_comm]

private lemma quotient_matrix (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    (ModuleCat.biproductIsoPi
        (fun _ : Fin a ↦ ModuleCat.of (ULift.{u + 1} (R l E n))
          (ULift.{u + 1} (R l E n)))).hom ≫
      differential l E n a b v ≫
      (ModuleCat.biproductIsoPi
        (fun _ : Fin b ↦ ModuleCat.of (ULift.{u + 1} (R l E n))
          (ULift.{u + 1} (R l E n)))).inv =
    biproduct.matrix (fun j i ↦ ModuleCat.ofHom
      (LinearMap.lsmul (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n))
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          (v i j))))) := by
  classical
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, ModuleCat.biproductIsoPi_inv_comp_π,
    biproduct.ι_matrix_assoc, biproduct.lift_π]
  have hι : biproduct.ι
      (fun _ : Fin a ↦ ModuleCat.of (ULift.{u + 1} (R l E n))
        (ULift.{u + 1} (R l E n))) j ≫
      (ModuleCat.biproductIsoPi _).hom =
      ModuleCat.ofHom (LinearMap.single (ULift.{u + 1} (R l E n))
        (fun _ : Fin a ↦ ULift.{u + 1} (R l E n)) j) := by
    apply (cancel_mono (ModuleCat.biproductIsoPi _).inv).mp
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [ModuleCat.biproductIsoPi_inv_comp_π]
    rw [biproduct.ι_π]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only []
    split_ifs <;> simp_all
  rw [← Category.assoc, ← Category.assoc, hι]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [differential, matrix, Matrix.mulVec, dotProduct, Pi.single_apply]

private def doubleComparison {C D Z : Type*} [Category* C] [Category* D] [Category* Z]
    [Preadditive C] [Preadditive D] [Preadditive Z]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject Z]
    (F : C ⥤ Z) (G : D ⥤ Z) [F.Additive] [G.Additive]
    {X₀ X₁ : C} {Y₀ Y₁ : D} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    (e₀ : F.obj X₀ ≅ G.obj Y₀) (e₁ : F.obj X₁ ≅ G.obj Y₁)
    (h : F.map f ≫ e₁.hom = e₀.hom ≫ G.map g) :
    (F.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.double f (i₀ := -1) (i₁ := 0) (by decide)) ≅
      (G.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.double g (i₀ := -1) (i₁ := 0) (by decide)) := by
  classical
  let hf : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let K := HomologicalComplex.double f hf
  let L := HomologicalComplex.double g hf
  let α : ∀ i : ℤ, F.obj (K.X i) ≅ G.obj (L.X i) := fun i ↦
    if h₀ : i = -1 then
      F.mapIso (eqToIso (congrArg K.X h₀) ≪≫ HomologicalComplex.doubleXIso₀ f hf) ≪≫
        e₀ ≪≫ (G.mapIso
          (eqToIso (congrArg L.X h₀) ≪≫ HomologicalComplex.doubleXIso₀ g hf)).symm
    else if h₁ : i = 0 then
      F.mapIso (eqToIso (congrArg K.X h₁) ≪≫
        HomologicalComplex.doubleXIso₁ f hf (by decide)) ≪≫ e₁ ≪≫
        (G.mapIso (eqToIso (congrArg L.X h₁) ≪≫
          HomologicalComplex.doubleXIso₁ g hf (by decide))).symm
    else (F.map_isZero (HomologicalComplex.isZero_double_X f hf i h₀ h₁)).iso
      (G.map_isZero (HomologicalComplex.isZero_double_X g hf i h₀ h₁))
  refine HomologicalComplex.Hom.isoOfComponents α ?_
  intro i j hij
  change (α i).hom ≫ G.map (L.d i j) = F.map (K.d i j) ≫ (α j).hom
  by_cases hi : i = -1
  · subst i
    have hj : j = 0 := by simpa using hij.symm
    rw [hj]
    dsimp only [α]
    simp only [dite_true, dite_false, show (0 : ℤ) ≠ -1 by decide,
      eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv]
    dsimp only [K, L]
    rw [HomologicalComplex.double_d f hf (by decide),
      HomologicalComplex.double_d g hf (by decide)]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
    simp only [G.map_id, Category.id_comp]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id,
      F.map_id, Category.id_comp]
    rw [← reassoc_of% h]
    simp only [Functor.map_comp, Category.assoc]
  · rw [HomologicalComplex.double_d_eq_zero₀ g hf i j hi,
      HomologicalComplex.double_d_eq_zero₀ f hf i j hi]
    simp

private lemma model_additive (T : Scheme.{u}) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (FiniteConstantModel.modelFunctor (A l E) T).Additive := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have : PreservesFiniteColimits (upperStarFromPoint T) := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesBinaryBiproducts (upperStarFromPoint T) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint T).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : ((upperStarFromPoint T).mapMod
      (Profinite.continuousCoefficientRingObj (A l E))).Additive :=
    { map_add := by intros; apply Mod.hom_ext; exact (upperStarFromPoint T).map_add }
  have : (FiniteConstantModel.scalarModules (A l E)).Additive :=
    FiniteConstantModel.scalarModules_additive _
  dsimp only [FiniteConstantModel.modelFunctor]
  infer_instance

/-- Ordinary quotient extension retains the matrix in normalized fixed coordinates.

Source: blueprint latest, integral ctf-equals-bc, Local models; Stacks Tags 03EK,
093M and 0G7E (blueprint: lem-sfb-finite-model-ordinary-free-complex).

Proof: identify the model of A^r with the r-fold direct sum of the integral
regular module, using its standard basis. Scalar extension preserves finite sums
and sends the regular module to the quotient regular module by the tensor unit
map. In normalized section coordinates the quotient regular module is the
constant free rank-one sheaf: the ring isomorphism in e sends every constant
scalar section to its canonical continuous constant section. After restricting
along constant scalars, the same identification is the constant module sheaf.
For the map v, compose with each basis inclusion and coordinate projection.
Each resulting scalar multiplication reduces by the actual quotient map and is
sent by the normalized encoding to multiplication by that residue. The matrix
maps therefore commute with the basis identifications. Map the double complex
termwise and use this commuting square to obtain the claimed cochain isomorphism.
Both constructions preserve the empty direct sum, covering ranks zero.
-/
theorem ordinary_free_complex (T : Scheme.{u}) (n : ℕ) (e : Encoding l E n T)
    (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    Nonempty
      ((((e.ordinary.trans e.fixed).functor.mapHomologicalComplex (.up ℤ)).obj
        (((Mod.extendScalars (AdicCompletion.quotient l E T n)).mapHomologicalComplex
            (.up ℤ)).obj
          (HomologicalComplex.double
            ((FiniteConstantModel.modelFunctor (A l E) T).map
              (integralDifferential l E a b v))
            (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)))) ≅
        (((constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).mapHomologicalComplex
            (.up ℤ)).obj (scalarComplex l E n a b v))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let F := FiniteConstantModel.modelFunctor (A l E) T ⋙
    Mod.extendScalars (AdicCompletion.quotient l E T n) ⋙
      (e.ordinary.trans e.fixed).functor
  let G := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
  have : (FiniteConstantModel.modelFunctor (A l E) T).Additive := model_additive l E T
  have : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  have : F.Additive := by dsimp only [F]; infer_instance
  have : HasFiniteBiproducts
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨i, hi⟩ := ordinary_scalar l E T n e
  let X := ModuleCat.of (A l E) (ULift.{u + 1} (A l E))
  let Y := ModuleCat.of (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n))
  let α (r : ℕ) := F.mapIso (ModuleCat.biproductIsoPi (fun _ : Fin r ↦ X)).symm ≪≫
    sumComparison F X r ≪≫ biproduct.mapIso (fun _ ↦ i) ≪≫
      (sumComparison G Y r).symm ≪≫ G.mapIso (ModuleCat.biproductIsoPi _)
  have hs : F.map (integralDifferential l E a b v) ≫ (α b).hom =
      (α a).hom ≫ G.map (differential l E n a b v) := by
    have hm := matrix_square F G i a b
      (fun j i ↦ ModuleCat.ofHom
        (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) (v i j)))
      (fun j i ↦ ModuleCat.ofHom
        (LinearMap.lsmul (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n))
          (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
            (v i j))))) (fun j i ↦ hi (v i j))
    rw [← integral_matrix l E a b v, ← quotient_matrix l E n a b v] at hm
    apply (cancel_epi (F.map (ModuleCat.biproductIsoPi (fun _ : Fin a ↦ X)).hom)).mp
    apply (cancel_mono (G.map (ModuleCat.biproductIsoPi (fun _ : Fin b ↦ Y)).inv)).mp
    dsimp only [α, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.symm_hom, Iso.symm_inv]
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
      F.map_id, Category.id_comp]
    simp only [← Category.assoc, ← G.map_comp, Iso.hom_inv_id,
      G.map_id, Category.comp_id]
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hm
  exact ⟨doubleComparison
    (Mod.extendScalars (AdicCompletion.quotient l E T n) ⋙
      (e.ordinary.trans e.fixed).functor) G
    ((FiniteConstantModel.modelFunctor (A l E) T).map (integralDifferential l E a b v))
    (differential l E n a b v) (α a) (α b) hs⟩

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
