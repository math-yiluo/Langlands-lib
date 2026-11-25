/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorConeComparison
import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.RingTheory.KoszulGeneratorChainMap
import WeilConjectures.RingTheory.KoszulProjectiveResolution
import WeilConjectures.RingTheory.KoszulPowerHomologyProZero
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Filtration
import WeilConjectures.RingTheory.KoszulConeHomologyProZero
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Algebra.Homology.BoundedDerivedTowerProZero
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.CategoryTheory.Triangulated.ProZeroMiddle
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.RingTheory.Noetherian.Basic
import all WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement

/-! # Pro-zero cones of the completed strict Koszul tensor augmentation

Source: Stacks Project, Tags 0921 and 099M.
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-cone-pro-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct

private theorem proZero_of_exact_realization
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : ℕ → CochainComplex C ℤ) (s : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (X : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ X.obj (op n))
    (he : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map (s n m h) ≫ (e n).hom =
      (e m).hom ≫ X.map (homOfLE h).op)
    (hz : ∀ n, ∃ m h, DerivedCategory.Q.map (s n m h) = 0) :
    ∀ n, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map (X.map (homOfLE h).op) = 0 := by
  intro n
  obtain ⟨m, h, hm⟩ := hz n
  refine ⟨m, h, ?_⟩
  have hE : ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L),
      QuasiIso f → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
    intro K L f hf
    have : QuasiIso f := hf
    infer_instance
  have hzE := CategoryTheory.localizedZero_map
    (E.mapHomologicalComplex (.up ℤ)) hE (s n m h) hm
  have hn := congrArg (fun f ↦ DerivedCategory.Q.map f) (he n m h)
  rw [Functor.map_comp, Functor.map_comp, hzE, zero_comp] at hn
  exact (cancel_epi (DerivedCategory.Q.map (e m).hom)).1 (hn.symm.trans (by simp))

-- Preserve the inherited name hq in the statement.
set_option linter.unusedVariables false in
/-- The strict tensor augmentation cone is eventually zero at each fixed level
in the derived category. No product, Roos fibre or derived limit occurs here.

Source: Stacks Project, More on Algebra, sequence-Koszul-complexes (Tag 0921),
and proetale.tex, lemma-naive-completion (Tag 099M).
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-cone-pro-zero).

Proof: the normalization and vanishing on the other total summands identify beta
with tensoring the finite coefficient augmentation. Over A, use the Noetherian
Koszul augmentation pro-zero theorem. Its Artin--Rees argument kills the negative
Koszul homology, and boundedness gives eventual vanishing of the cone maps in
D(A). Generator-power ideals are cofinal with powers of I: counting exponents
in monomials gives I^(r*n+1) contained in (a_i^(n+1)). Thus the strict augmentation
to A/I^(n+1) has pro-zero cones. Exact constant sheafification and flat completed
scalar extension carry these zero derived maps to zero maps over the completed
coefficient sheaf. Finite coefficient identification carries the quotient maps
to the recorded finite function modules. Tensoring with the K-flat P descends
to an additive functor on the derived category, hence preserves zero morphisms.
The tensor-cone comparison multiplies the shifted source summand in tensor degree
p by (-1)^p; it commutes with the actual strict cone transitions. Transposing the
tower and complex indices gives exactly the cone in the conclusion. This uses
no boundedness of P and does not interchange tensor with an infinite product.
For r=0 the coefficient augmentation is an isomorphism; I=A and the zero ring
are covered by the same algebraic pro-zero theorem. -/
theorem completedKoszulTensorQuotientConeProZero
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (hu : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
      completedAdicKoszulTensorUnit T d r a P n ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
          completedQuotientTensorUnit T d P n)
    (hz : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
      completedKoszulTensorSummand T d r a P n p q ≫
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (β.app P)).app (op n)).f (p + q) = 0)
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map
      ((CochainComplex.mappingCone (β.app P)).asFunctor.map (homOfLE h).op) = 0 := by
  let := d.noetherian
  let : IsNoetherianRing (ULift.{t + 1} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let := HasDerivedCategory.standard (ModuleCat.{t + 1} (ULift.{t + 1} A))
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  obtain ⟨εA, sA, qA, hεA, hsA, hqA, hc, hzero⟩ :=
    ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero
      (ULift.{t + 1} A) r (fun i ↦ ULift.up (a i))
  obtain ⟨E, hadd, hlim, hcolim, e, he⟩ :=
    completedKoszulCoefficientConeRealization T d r a ha
      εA sA qA hεA hsA hqA hc (β.app U) (hu U) (hz U)
  have hcoef : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map
      ((CochainComplex.mappingCone (β.app U)).asFunctor.map (homOfLE h).op) = 0 :=
    proZero_of_exact_realization E _ _ _ e he hzero
  obtain ⟨c⟩ := completedKoszulTensorConeComparison T d r a β hu hz P
  apply CategoryTheory.proZero_of_towerIso c
  intro n
  obtain ⟨m, h, hm⟩ := hcoef n
  refine ⟨m, h, ?_⟩
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  have : (tensorLeft P).PreservesZeroMorphisms := by
    constructor
    intro K L
    change HomologicalComplex.mapBifunctorMap (𝟙 P) (0 : K ⟶ L)
      (curriedTensor _) (.up ℤ) = 0
    exact CategoryTheory.mapBifunctorMap_id_zero (curriedTensor _) P K L
  exact CategoryTheory.localizedZero_map (tensorLeft P)
    (fun f hf ↦ CategoryTheory.flatConstantTensor_preservesQuasiIso
      (O := completedAdicCommRing T d) (ProEt.topology T) P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
        (R := completedAdicCommRing T d) P).2 hP) f hf)
    ((CochainComplex.mappingCone (β.app U)).asFunctor.map (homOfLE h).op) hm

end AlgebraicGeometry.Scheme
