/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels

/-! # Data for the finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

/-- The strict Koszul tensor tower, with complexes and tower indices transposed.
Its objects and maps are the recorded total tensors, not chosen replacements.
Source: Stacks Tag 099M
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-augmentation). -/
@[reducible] def completedKoszulTensorTower (r : ℕ) (a : Fin r → A) :
    CochainComplex (CompletedAdicModules T d) ℤ ⥤
      CochainComplex (CompletedAdicTowers T d) ℤ :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  let F := curriedTensor (CompletedAdicModules T d)
  let τ := (HomologicalComplex.functorEquivalence
    (CompletedAdicModules T d) (.up ℤ) ℕᵒᵖ).inverse
  { obj := fun P ↦ τ.obj (Functor.ofOpSequence (completedAdicKoszulTensorStep T d r a P))
    map := fun {P P'} f ↦ τ.map (NatTrans.ofOpSequence
      (fun n ↦ HomologicalComplex.mapBifunctorMap f (𝟙 (completedAdicKoszul T d r a n))
        F (.up ℤ)) (fun n ↦ by
          simp only [Functor.ofOpSequence_map_homOfLE_succ]
          change HomologicalComplex.mapBifunctorMap (𝟙 P)
              (completedAdicKoszulStep T d r a n) F (.up ℤ) ≫
                HomologicalComplex.mapBifunctorMap f (𝟙 _) F (.up ℤ) =
            HomologicalComplex.mapBifunctorMap f (𝟙 _) F (.up ℤ) ≫
              HomologicalComplex.mapBifunctorMap (𝟙 P')
                (completedAdicKoszulStep T d r a n) F (.up ℤ)
          exact (F.map₂CochainComplex.map f).naturality (completedAdicKoszulStep T d r a n)))
    map_id := fun P ↦ by
      apply HomologicalComplex.hom_ext
      intro q
      apply NatTrans.ext
      funext n
      change (HomologicalComplex.mapBifunctorMap (𝟙 P)
        (𝟙 (completedAdicKoszul T d r a n.unop)) F (.up ℤ)).f q = 𝟙 _
      exact HomologicalComplex.congr_hom
        (NatTrans.congr_app ((F.map₂CochainComplex).map_id P)
          (completedAdicKoszul T d r a n.unop)) q
    map_comp := fun {P P' P''} f g ↦ by
      rw [← τ.map_comp]
      congr 1
      apply NatTrans.ext
      funext n
      apply HomologicalComplex.hom_ext
      intro q
      change (HomologicalComplex.mapBifunctorMap (f ≫ g)
          (𝟙 (completedAdicKoszul T d r a n.unop)) F (.up ℤ)).f q =
        (HomologicalComplex.mapBifunctorMap f
          (𝟙 (completedAdicKoszul T d r a n.unop)) F (.up ℤ)).f q ≫
          (HomologicalComplex.mapBifunctorMap g
            (𝟙 (completedAdicKoszul T d r a n.unop)) F (.up ℤ)).f q
      exact HomologicalComplex.congr_hom
        (NatTrans.congr_app ((F.map₂CochainComplex).map_comp f g)
          (completedAdicKoszul T d r a n.unop)) q }

/-- The actual finite quotient tensor map, specified independently of the Koszul complex.
Source: Stacks Tag 099M
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-augmentation). -/
def completedQuotientTensorUnit
    (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) :
    P ⟶ (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P).asFunctor.obj
      (op n) :=
  (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app P ≫
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
      (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P)

/-- The injection of one actual total tensor summand.
Source: Stacks Tag 099M
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-augmentation). -/
def completedKoszulTensorSummand (r : ℕ) (a : Fin r → A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) :
    ((curriedTensor (CompletedAdicModules T d)).obj (P.X p)).obj
        ((completedAdicKoszul T d r a n).X q) ⟶
      (completedAdicKoszulTensor T d r a P n).X (p + q) :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  HomologicalComplex.ιMapBifunctor P (completedAdicKoszul T d r a n)
    (curriedTensor _) (.up ℤ) p q (p + q) rfl

end AlgebraicGeometry.Scheme
