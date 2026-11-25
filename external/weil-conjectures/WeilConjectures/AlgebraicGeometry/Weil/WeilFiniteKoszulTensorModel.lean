/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal

/-! # An algebraic intermediate for the finite Koszul comparison

The ordered tensor is formed over the original coefficient ring, before sheafification
or coefficient extension. Its factors are the existing one-generator exterior complexes.
Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: def-weil-pbc-finite-negative-koszul-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

/-- The algebraic exterior unit, including cohomological reindexing.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-finite-negative-koszul-tensor). -/
def finiteKoszulExteriorUnitZero (r : ℕ) (a : Fin r → A) (m : ℕ) :
    ModuleCat.of A A ⟶ (completedKoszulPower (A := A) r a m).X 0 :=
  ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap ≫
    ((ExteriorAlgebra.koszulComplex A r (fun k ↦ a k ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) rfl).inv

/-- The ordered tensor of the one-generator negative Koszul complexes.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-finite-negative-koszul-tensor). -/
def finiteNegativeKoszulTensor : (r : ℕ) → (Fin r → A) → ℕ →
    CochainComplex (ModuleCat.{u + 1} A) ℤ
  | 0, _, _ => (HomologicalComplex.single _ (.up ℤ) 0).obj (ModuleCat.of A A)
  | r + 1, a, m => HomologicalComplex.tensorObj
      (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
      (finiteNegativeKoszulTensor r (fun i ↦ a i.succ) m)

/-- The strict tensor of the one-generator diagonal transitions.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-finite-negative-koszul-tensor). -/
def finiteNegativeKoszulTransition : (r : ℕ) → (a : Fin r → A) → (m : ℕ) →
    finiteNegativeKoszulTensor r a (m + 1) ⟶ finiteNegativeKoszulTensor r a m
  | 0, _, _ => 𝟙 _
  | r + 1, a, m => HomologicalComplex.tensorHom
      (completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m)
      (finiteNegativeKoszulTransition r (fun i ↦ a i.succ) m)

/-- The tensor of the degree-zero algebraic units, in its degree-zero summand.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-finite-negative-koszul-tensor). -/
def finiteNegativeKoszulUnitZero : (r : ℕ) → (a : Fin r → A) → (m : ℕ) →
    ModuleCat.of A A ⟶ (finiteNegativeKoszulTensor r a m).X 0
  | 0, _, _ => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv
  | r + 1, a, m =>
      (ρ_ (ModuleCat.of A A)).inv ≫
        (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a 0) m ⊗ₘ
          finiteNegativeKoszulUnitZero r (fun i ↦ a i.succ) m) ≫
        HomologicalComplex.ιTensorObj
          (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
          (finiteNegativeKoszulTensor r (fun i ↦ a i.succ) m) 0 0 0 (by omega)

end AlgebraicGeometry.Scheme
