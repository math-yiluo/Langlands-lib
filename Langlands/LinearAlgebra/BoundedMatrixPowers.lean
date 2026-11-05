import Langlands.LinearAlgebra.IntegralMatrixCharpoly
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral

/-! # A finite matrix lattice and bounded powers -/

noncomputable section

namespace Langlands.LinearAlgebra

open Polynomial

section Algebra

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B] [IsNoetherianRing R]

/-- Powers contained in one finite module make an algebra element integral. -/
theorem isIntegral_of_powers_mem_fg (x : B) (L : Submodule R B) (hL : L.FG)
    (hx : ∀ k : ℕ, x ^ k ∈ L) : IsIntegral R x := by
  have hle : (Algebra.adjoin R {x}).toSubmodule ≤ L := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hx k
  exact IsIntegral.of_mem_of_fg _ (hL.of_le hle) x (Algebra.subset_adjoin rfl)

end Algebra

section Lattice

variable (R : Type*) {F n : Type*} [CommRing R] [Field F] [Algebra R F]
  [Fintype n] [DecidableEq n]

/-- The coefficient inclusion followed by multiplication by a field scalar. -/
def scaledMatrixLatticeMap (b : F) :
    Matrix n n R →ₗ[R] Matrix n n F :=
  ((LinearMap.lsmul F (Matrix n n F) b).restrictScalars R).comp
    (Algebra.ofId R F).mapMatrix.toLinearMap

/-- The scalar multiple of the standard integral matrix lattice. -/
def scaledMatrixLattice (b : F) : Submodule R (Matrix n n F) :=
  (scaledMatrixLatticeMap R b).range

theorem scaledMatrixLattice_fg (b : F) : (scaledMatrixLattice R (n := n) b).FG :=
  Submodule.fg_range _

theorem mem_scaledMatrixLattice_iff (b : F) (A : Matrix n n F) :
    A ∈ scaledMatrixLattice R b ↔
      ∃ M : Matrix n n R, ∀ i j, b * algebraMap R F (M i j) = A i j := by
  change (∃ M, scaledMatrixLatticeMap R b M = A) ↔ _
  simp only [scaledMatrixLatticeMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.lsmul_apply, AlgHom.toLinearMap_apply, AlgHom.mapMatrix_apply]
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M, fun _ _ ↦ rfl⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, Matrix.ext fun i j ↦ hM i j⟩

end Lattice

section Valuation

open ValuativeRel

variable {F n : Type*} [Field F] [ValuativeRel F] [Fintype n] [DecidableEq n]

theorem mem_scaledMatrixLattice_of_entry_bound {b : F} (hb : b ≠ 0)
    (A : Matrix n n F) (hA : ∀ i j, A i j ≤ᵥ b) :
    A ∈ scaledMatrixLattice (valuation F).integer b := by
  apply (mem_scaledMatrixLattice_iff _ _ _).mpr
  let M : Matrix n n (valuation F).integer := fun i j ↦
    ⟨A i j / b, (valuation F).vle_one_iff.mp ((div_vle_one_iff hb).mpr (hA i j))⟩
  refine ⟨M, fun i j ↦ ?_⟩
  change b * (A i j / b) = A i j
  exact mul_div_cancel₀ _ hb

/-- A common entry bound on all nonnegative powers forces matrix integrality. -/
theorem isIntegral_matrix_of_bounded_powers
    [IsNoetherianRing (valuation F).integer] (A : Matrix n n F)
    (hA : ∃ b : F, b ≠ 0 ∧ ∀ k : ℕ, ∀ i j, (A ^ k) i j ≤ᵥ b) :
    IsIntegral (valuation F).integer A := by
  obtain ⟨b, hb, hA⟩ := hA
  exact isIntegral_of_powers_mem_fg A (scaledMatrixLattice (valuation F).integer b)
    (scaledMatrixLattice_fg _ _) fun k ↦
      mem_scaledMatrixLattice_of_entry_bound hb (A ^ k) (hA k)

/-- The coefficient bound follows from bounded matrix powers over a local field. -/
theorem charpoly_coeff_vle_one_of_bounded_powers [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (A : Matrix n n F)
    (hA : ∃ b : F, b ≠ 0 ∧ ∀ k : ℕ, ∀ i j, (A ^ k) i j ≤ᵥ b) (i : ℕ) :
    A.charpoly.coeff i ≤ᵥ (1 : F) := by
  have h : IsIntegral (valuation F).integer (A.charpoly.coeff i) :=
    isIntegral_charpoly_coeff (isIntegral_matrix_of_bounded_powers A hA) i
  exact (valuation F).vle_one_iff.mpr
    ((Valuation.integer.integers (valuation F)).isIntegral_iff_v_le_one.mp h)

end Valuation

end Langlands.LinearAlgebra
