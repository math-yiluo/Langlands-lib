import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement

/-!
# Bounded cyclic decomposition of an annihilated polynomial module: proof

This module proves `Langlands.PolynomialModuleBoundedCyclicDecompositionStatement`
from Mathlib's structure theorem for finitely generated torsion modules over a
principal ideal domain, `Module.equiv_directSum_of_isTorsion`.
-/

namespace Langlands

open Polynomial

universe uK uV

namespace PolynomialModuleBoundedCyclicDecomposition

/-- Restricting a product to the factors satisfying `P` is a linear equivalence
when every factor outside `P` is trivial. -/
def piRestrictOfSubsingleton {R : Type*} [Semiring R] {ι : Type*} (P : ι → Prop)
    [DecidablePred P] (Q : ι → Type*) [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]
    (h : ∀ i, ¬ P i → Subsingleton (Q i)) :
    ((i : ι) → Q i) ≃ₗ[R] ((i : {i // P i}) → Q i) where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y i := if hi : P i then y ⟨i, hi⟩ else 0
  left_inv x := by
    funext i
    by_cases hi : P i
    · simp [hi]
    · have := h i hi
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]

/-- The bounded monic form of a decomposition of `Module.AEval' f` as a finite
product of cyclic quotients `K[X] ⧸ (r i)`, when a nonzero `c` annihilates `f`. -/
theorem exists_bounded_of_equiv_pi {K : Type uK} [Field K] {V : Type uV} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V) {c : K[X]} (hc0 : c ≠ 0)
    (hc : aeval f c = 0) {ι : Type*} [Fintype ι] (r : ι → K[X])
    (E : Module.AEval' f ≃ₗ[K[X]] ((i : ι) → K[X] ⧸ Ideal.span ({r i} : Set K[X]))) :
    ∃ (m : ℕ) (q : Fin m → K[X]),
      m ≤ Module.finrank K V ∧
        (∀ i, (q i).Monic ∧ q i ∣ c) ∧
        Nonempty (Module.AEval' f ≃ₗ[K[X]]
          ((i : Fin m) → K[X] ⧸ Ideal.span ({q i} : Set K[X]))) := by
  classical
  -- `c` annihilates the product.
  have hsmul : ∀ y : ((i : ι) → K[X] ⧸ Ideal.span ({r i} : Set K[X])), c • y = 0 := by
    intro y
    have h1 : c • E.symm y = 0 :=
      (Module.AEval.of K V f).symm.injective <| by simp [hc]
    calc c • y = E (c • E.symm y) := by rw [map_smul, LinearEquiv.apply_symm_apply]
      _ = 0 := by rw [h1, map_zero]
  -- Hence every `r i` divides `c`, and in particular is nonzero.
  have hdiv : ∀ i, r i ∣ c := by
    intro i
    have h := congrFun (hsmul (Pi.single i (Submodule.Quotient.mk 1))) i
    rw [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, ← Submodule.Quotient.mk_smul,
      smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero] at h
    exact Ideal.mem_span_singleton.mp h
  have hr0 : ∀ i, r i ≠ 0 := fun i h => hc0 (zero_dvd_iff.mp (h ▸ hdiv i))
  -- Drop the factors presented by units.
  have hsub : ∀ i, ¬ ¬ IsUnit (r i) →
      Subsingleton (K[X] ⧸ Ideal.span ({r i} : Set K[X])) := by
    intro i hi
    rw [Submodule.Quotient.subsingleton_iff]
    exact Ideal.span_singleton_eq_top.mpr (not_not.mp hi)
  let S := {i // ¬ IsUnit (r i)}
  let σ : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let r' : Fin (Fintype.card S) → K[X] := fun j => r (σ.symm j)
  let q : Fin (Fintype.card S) → K[X] := fun j => normalize (r' j)
  have hspan : ∀ j, Ideal.span ({r' j} : Set K[X]) = Ideal.span ({q j} : Set K[X]) :=
    fun j => Ideal.span_singleton_eq_span_singleton.mpr (associated_normalize _)
  let E' : Module.AEval' f ≃ₗ[K[X]]
      ((j : Fin (Fintype.card S)) → K[X] ⧸ Ideal.span ({q j} : Set K[X])) :=
    ((E.trans (piRestrictOfSubsingleton (fun i => ¬ IsUnit (r i))
      (fun i => K[X] ⧸ Ideal.span ({r i} : Set K[X])) hsub)).trans
      (LinearEquiv.piCongrLeft' K[X] (fun s : S => K[X] ⧸ Ideal.span ({r s} : Set K[X])) σ)).trans
      (LinearEquiv.piCongrRight fun j => Submodule.quotEquivOfEq _ _ (hspan j))
  refine ⟨Fintype.card S, q, ?_, fun j => ⟨Polynomial.monic_normalize (hr0 _),
    normalize_dvd_iff.mpr (hdiv _)⟩, ⟨E'⟩⟩
  -- The bound: one nonzero vector in each remaining factor.
  have hnt : ∀ j, Nontrivial (K[X] ⧸ Ideal.span ({q j} : Set K[X])) := by
    intro j
    rw [Submodule.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (σ.symm j).2 ((normalize_associated (r' j)).isUnit_iff.mp hu)
  have : Module.Finite K
      ((j : Fin (Fintype.card S)) → K[X] ⧸ Ideal.span ({q j} : Set K[X])) :=
    Module.Finite.equiv (E'.restrictScalars K)
  let φ : (Fin (Fintype.card S) → K) →ₗ[K]
      ((j : Fin (Fintype.card S)) → K[X] ⧸ Ideal.span ({q j} : Set K[X])) :=
    LinearMap.pi fun j => (LinearMap.proj j).smulRight (1 : K[X] ⧸ Ideal.span ({q j} : Set K[X]))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    funext j
    have h := congrFun ha j
    simp only [φ, LinearMap.pi_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Pi.zero_apply] at h
    by_contra hj
    have h1 := inv_smul_smul₀ hj (1 : K[X] ⧸ Ideal.span ({q j} : Set K[X]))
    rw [h, smul_zero] at h1
    exact zero_ne_one h1
  calc Fintype.card S = Module.finrank K (Fin (Fintype.card S) → K) :=
        (Module.finrank_fin_fun K).symm
    _ ≤ Module.finrank K
          ((j : Fin (Fintype.card S)) → K[X] ⧸ Ideal.span ({q j} : Set K[X])) :=
        LinearMap.finrank_le_finrank_of_injective hφ
    _ = Module.finrank K (Module.AEval' f) := (E'.restrictScalars K).finrank_eq.symm
    _ = Module.finrank K V := (Module.AEval.of K V f).finrank_eq.symm

end PolynomialModuleBoundedCyclicDecomposition

open PolynomialModuleBoundedCyclicDecomposition in
/-- Proof of `PolynomialModuleBoundedCyclicDecompositionStatement`. -/
theorem polynomialModuleBoundedCyclicDecomposition :
    PolynomialModuleBoundedCyclicDecompositionStatement.{uK, uV} := by
  intro K _ V _ _ _ f c hc0 hc
  have htors : Module.IsTorsion K[X] (Module.AEval' f) :=
    Module.AEval.isTorsion_of_aeval_eq_zero hc hc0
  obtain ⟨ι, _, p, -, e, ⟨E⟩⟩ := Module.equiv_directSum_of_isTorsion htors
  exact exists_bounded_of_equiv_pi f hc0 hc (fun i => p i ^ e i)
    (E.trans (DirectSum.linearEquivFunOnFintype K[X] ι _))

end Langlands
