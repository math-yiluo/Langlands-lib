/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationData
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulUnitZeroIso
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientProjection
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
import all WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality

/-! # Existence of the finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
(blueprint: new-y2-completed-koszul-tensor-quotient-augmentation-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] WeilConjectures.sfAbSheafify

attribute [local instance] WeilConjectures.sfAbBijective

attribute [local instance] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.defeqAttrib.useBackward true in
private theorem tensorSingle_ι
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    (F : C ⥤ C ⥤ C) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (P : CochainComplex C ℤ) (B : C)
    [HomologicalComplex.HasMapBifunctor P ((HomologicalComplex.single C (.up ℤ) 0).obj B)
      F (.up ℤ)] (i : ℤ) :
    HomologicalComplex.ιMapBifunctor P ((HomologicalComplex.single C (.up ℤ) 0).obj B)
        F (.up ℤ) i 0 i (Int.add_zero i) ≫
      (CochainComplex.mapBifunctorSingle₂Iso F B P).hom.f i =
        (F.obj (P.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom := by
  dsimp [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

section TensorNaturality

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  (F : C ⥤ C ⥤ C) [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]
  [∀ P Q : CochainComplex C ℤ, HomologicalComplex.HasMapBifunctor P Q F (.up ℤ)]

private theorem tensorProjection_step (P K K' : CochainComplex C ℤ)
    {B B' : C} (f : K' ⟶ K)
    (e : K ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj B)
    (e' : K' ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj B') (g : B' ⟶ B)
    (h : f ≫ e = e' ≫ (HomologicalComplex.single C (.up ℤ) 0).map g) :
    HomologicalComplex.mapBifunctorMap (𝟙 P) f F (.up ℤ) ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 P) e F (.up ℤ) ≫
          (CochainComplex.mapBifunctorSingle₂Iso F B P).hom) =
      (HomologicalComplex.mapBifunctorMap (𝟙 P) e' F (.up ℤ) ≫
        (CochainComplex.mapBifunctorSingle₂Iso F B' P).hom) ≫
          (NatTrans.mapHomologicalComplex (F.flip.map g) (.up ℤ)).app P := by
  let H := F.map₂CochainComplex.obj P
  change H.map f ≫ (H.map e ≫ _) = (H.map e' ≫ _) ≫ _
  rw [← Category.assoc, ← H.map_comp, h, H.map_comp, Category.assoc]
  exact (congrArg (fun k ↦ H.map e' ≫ k)
    (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality₂ F g P)).trans
      (Category.assoc _ _ _).symm

private theorem tensorProjection_naturality {P P' K : CochainComplex C ℤ}
    (f : P ⟶ P') {B : C}
    (e : K ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj B) :
    HomologicalComplex.mapBifunctorMap f (𝟙 K) F (.up ℤ) ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 P') e F (.up ℤ) ≫
          (CochainComplex.mapBifunctorSingle₂Iso F B P').hom) =
      (HomologicalComplex.mapBifunctorMap (𝟙 P) e F (.up ℤ) ≫
        (CochainComplex.mapBifunctorSingle₂Iso F B P).hom) ≫
          ((F.flip.obj B).mapHomologicalComplex (.up ℤ)).map f := by
  have hn := (F.map₂CochainComplex.map f).naturality e
  change HomologicalComplex.mapBifunctorMap (𝟙 P) e F (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap f (𝟙 _) F (.up ℤ) =
    HomologicalComplex.mapBifunctorMap f (𝟙 _) F (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') e F (.up ℤ) at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  exact (congrArg (fun k ↦ HomologicalComplex.mapBifunctorMap (𝟙 P) e F (.up ℤ) ≫ k)
    (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality F B f)).trans
      (Category.assoc _ _ _).symm

private theorem tensorProjection_unit [MonoidalCategory C]
    [(curriedTensor C).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor C).obj X).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex C ℤ,
      HomologicalComplex.HasMapBifunctor P Q (curriedTensor C) (.up ℤ)]
    (P K : CochainComplex C ℤ) (B : C)
    (e : K ⟶ (HomologicalComplex.single C (.up ℤ) 0).obj B)
    (u : 𝟙_ C ⟶ K.X 0) (b : 𝟙_ C ⟶ B)
    (hu : u ≫ e.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom = b)
    (j : ℤ) :
    (ρ_ (P.X j)).inv ≫ ((curriedTensor C).obj (P.X j)).map u ≫
        HomologicalComplex.ιMapBifunctor P K (curriedTensor C) (.up ℤ) j 0 j (Int.add_zero j) ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 P) e (curriedTensor C) (.up ℤ) ≫
            (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P).hom).f j =
      (ρ_ (P.X j)).inv ≫ ((curriedTensor C).obj (P.X j)).map b := by
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  rw [tensorSingle_ι]
  change (ρ_ (P.X j)).inv ≫ ((curriedTensor C).obj (P.X j)).map u ≫
      ((curriedTensor C).map (𝟙 (P.X j))).app (K.X 0) ≫
        ((curriedTensor C).obj (P.X j)).map (e.f 0) ≫
          ((curriedTensor C).obj (P.X j)).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom = _
  rw [show ((curriedTensor C).map (𝟙 (P.X j))).app (K.X 0) = 𝟙 _ from
    NatTrans.congr_app ((curriedTensor C).map_id (P.X j)) (K.X 0)]
  simp only [Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp, hu]

end TensorNaturality

private theorem coefficientAugmentation
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ ε : ∀ n : ℕ, completedAdicKoszul T d r a n ⟶
        (HomologicalComplex.single (CompletedAdicModules T d) (.up ℤ) 0).obj
          (completedAdicFiniteModule T d n),
      (∀ n, completedAdicKoszulUnitZero T d r a n ≫ (ε n).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
          reconstructionQuotientUnit T d n) ∧
      (∀ n, completedAdicKoszulStep T d r a n ≫ ε n =
        ε (n + 1) ≫ (HomologicalComplex.single (CompletedAdicModules T d) (.up ℤ) 0).map
          (completedAdicFiniteModuleStep T d n)) := by
  let (n : ℕ) : IsIso (completedAdicKoszulUnitZero T d r a n) :=
    completedKoszulUnitZero_isIso T d r a n
  choose p hp hcycle using fun n ↦ completedKoszulQuotientProjection_exists T d r a ha n
  have hd (n : ℕ) (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
      (completedAdicKoszul T d r a n).d i 0 ≫ p n = 0 := by
    have : i = -1 := by change i + 1 = 0 at hi; omega
    subst i
    exact hcycle n
  let ε (n : ℕ) := HomologicalComplex.mkHomToSingle (p n) (hd n)
  have he (n : ℕ) : (ε n).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom = p n := by
    dsimp only [ε]
    rw [HomologicalComplex.mkHomToSingle_f]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨ε, fun n ↦ ?_, fun n ↦ ?_⟩
  · rw [he]
    exact hp n
  · apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom).1
    dsimp only [HomologicalComplex.comp_f]
    rw [Category.assoc, he]
    apply (cancel_epi (completedAdicKoszulUnitZero T d r a (n + 1))).1
    rw [← Category.assoc, adicKoszulUnitZero_transition, hp]
    simp only [Category.assoc, HomologicalComplex.single_map_f_self]
    rw [← Category.assoc ((ε (n + 1)).f 0), he, ← Category.assoc, hp]
    exact (reconstructionQuotientUnit_step T d n).symm

private theorem assembleTowerMap {C D : Type*} [Category C] [HasZeroMorphisms C]
    [Category D] (X Y : D ⥤ CochainComplex (ℕᵒᵖ ⥤ C) ℤ)
    (v : ∀ (P : D) (n : ℕ),
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj (X.obj P)).obj (op n) ⟶
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj (Y.obj P)).obj (op n))
    (hs : ∀ P n j, ((X.obj P).X j).map (homOfLE (Nat.le_succ n)).op ≫ (v P n).f j =
      (v P (n + 1)).f j ≫ ((Y.obj P).X j).map (homOfLE (Nat.le_succ n)).op)
    (hn : ∀ {P P'} (f : P ⟶ P') n j,
      ((X.map f).f j).app (op n) ≫ (v P' n).f j =
        (v P n).f j ≫ ((Y.map f).f j).app (op n)) :
    ∃ β : X ⟶ Y, ∀ P n,
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
        v P n := by
  let β : X ⟶ Y :=
    { app := fun P ↦
        { f := fun j ↦ NatTrans.ofOpSequence (fun n ↦ (v P n).f j) (fun n ↦ hs P n j)
          comm' := fun i j _ ↦ by
            apply NatTrans.ext
            funext n
            exact (v P n.unop).comm i j }
      naturality := fun P P' f ↦ by
        apply HomologicalComplex.hom_ext
        intro j
        apply NatTrans.ext
        funext n
        exact hn f n.unop j }
  refine ⟨β, fun P n ↦ ?_⟩
  apply HomologicalComplex.hom_ext
  intro j
  rfl

set_option linter.unusedVariables false in
/-- The normalized strict augmentation exists before taking any products.

Source: Stacks Project, Tags 091N and 099M, the degree-zero augmentation in the
proof of lemma-naive-completion.
(blueprint: new-y2-completed-koszul-tensor-quotient-augmentation-exists).

Proof: augment the exterior Koszul complex on the powers a_i^(n+1) to
A/I^(n+1), then apply constant realization, completed scalar extension, and the
actual total tensor construction. The degree-zero quotient map sends the Koszul
unit to the recorded quotient unit; every nonzero exterior summand is sent to
zero. The differential condition follows because each generator power belongs
to I^(n+1), and the diagonal successors commute with the quotient maps. -/
theorem completedKoszulTensorQuotientAugmentation_exists
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ β : completedKoszulTensorTower T d r a ⟶
        (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ),
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
        completedAdicKoszulTensorUnit T d r a P n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
            completedQuotientTensorUnit T d P n) ∧
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        completedKoszulTensorSummand T d r a P n p q ≫
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
              (β.app P)).app (op n)).f (p + q) = 0) := by
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  let : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  let : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  let F := curriedTensor (CompletedAdicModules T d)
  let S := HomologicalComplex.single (CompletedAdicModules T d) (.up ℤ) 0
  obtain ⟨ε, hunit, hstep⟩ := coefficientAugmentation T d r a ha
  let v (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) :
      completedAdicKoszulTensor T d r a P n ⟶
        ((F.flip.obj (completedAdicFiniteModule T d n)).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.mapBifunctorMap (𝟙 P) (ε n) F (.up ℤ) ≫
      (CochainComplex.mapBifunctorSingle₂Iso F (completedAdicFiniteModule T d n) P).hom
  have hvstep (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) :
      completedAdicKoszulTensorStep T d r a P n ≫ v P n =
        v P (n + 1) ≫
          (NatTrans.mapHomologicalComplex (F.flip.map (completedAdicFiniteModuleStep T d n))
            (.up ℤ)).app P := by
    exact tensorProjection_step F P _ _ (completedAdicKoszulStep T d r a n)
      (ε n) (ε (n + 1)) (completedAdicFiniteModuleStep T d n) (hstep n)
  have hvnat {P P' : CochainComplex (CompletedAdicModules T d) ℤ} (f : P ⟶ P') (n : ℕ) :
      HomologicalComplex.mapBifunctorMap f (𝟙 (completedAdicKoszul T d r a n))
          F (.up ℤ) ≫ v P' n =
        v P n ≫ ((F.flip.obj (completedAdicFiniteModule T d n)).mapHomologicalComplex
          (.up ℤ)).map f := by
    exact tensorProjection_naturality F f (ε n)
  obtain ⟨β, hβ⟩ := assembleTowerMap (completedKoszulTensorTower T d r a)
    ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)) v
    (fun P n j ↦ by
      change (((Functor.ofOpSequence (completedAdicKoszulTensorStep T d r a P)).map
          (homOfLE (Nat.le_succ n)).op).f j) ≫ (v P n).f j =
        (v P (n + 1)).f j ≫
          ((Functor.ofOpSequence
            (X := fun k ↦ F.flip.obj (completedAdicFiniteModule T d k))
            (fun k ↦ F.flip.map (completedAdicFiniteModuleStep T d k))).map
              (homOfLE (Nat.le_succ n)).op).app (P.X j)
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact HomologicalComplex.congr_hom (hvstep P n) j)
    (fun f n j ↦ HomologicalComplex.congr_hom (hvnat f n) j)
  refine ⟨β, ?_, ?_⟩
  · intro P n
    rw [hβ]
    apply HomologicalComplex.hom_ext
    intro j
    have hh := tensorProjection_unit P (completedAdicKoszul T d r a n)
      (completedAdicFiniteModule T d n) (ε n)
      (completedAdicKoszulUnitZero T d r a n) (reconstructionQuotientUnit T d n)
      (hunit n) j
    exact hh.trans
      ((reconstructionOrdinaryUnit_exists T d).exists.choose_spec (P.X j) n).symm
  · intro P n p q hq
    rw [hβ]
    dsimp only [completedKoszulTensorSummand, v, HomologicalComplex.comp_f]
    rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    have hz : IsZero ((S.obj (completedAdicFiniteModule T d n)).X q) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hq
    have he : (ε n).f q = 0 := hz.eq_of_tgt _ _
    rw [he, Functor.map_zero, zero_comp, comp_zero]

end AlgebraicGeometry.Scheme
