import Langlands.LinearAlgebra.CyclicCentralizerWitness
import Langlands.LinearAlgebra.MatrixConjugationConormal
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Adjusted transpose on the conormal to matrix conjugation and central directions -/

noncomputable section

open Matrix Polynomial

set_option autoImplicit false

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The trace conormal after adjoining the directions `Z` to the orbit tangent. -/
def matrixConormalWith (C : Mat) (Z : Submodule ℝ Mat) : Submodule ℝ Mat :=
  matrixTraceBilin.orthogonal (LinearMap.range (matrixConjugationTangent C) ⊔ Z)

theorem mem_matrixConormalWith_iff {C A : Mat} {Z : Submodule ℝ Mat} :
    A ∈ matrixConormalWith C Z ↔ Commute C A ∧ A ∈ matrixTraceBilin.orthogonal Z := by
  constructor
  · intro h
    exact ⟨(mem_matrixTraceBilin_orthogonal_conjugationTangent_iff C A).mp
      (LinearMap.BilinForm.orthogonal_le le_sup_left h),
      LinearMap.BilinForm.orthogonal_le le_sup_right h⟩
  · rintro ⟨hC, hZ⟩
    have hT := (mem_matrixTraceBilin_orthogonal_conjugationTangent_iff C A).mpr hC
    intro X hX
    obtain ⟨U, hU, V, hV, rfl⟩ := Submodule.mem_sup.mp hX
    rw [map_add, LinearMap.add_apply, hT U hU, hZ V hV, add_zero]

private theorem trace_orthogonal_projection_commutes (Z : Submodule ℝ Mat)
    (h : IsCompl (matrixTraceBilin.orthogonal Z) Z) (L : Mat →ₗ[ℝ] Mat)
    (hB : ∀ X Y : Mat, matrixTraceBilin (L X) (L Y) = matrixTraceBilin X Y)
    (hZ : ∀ z ∈ Z, L z = z) (X : Mat) :
    (matrixTraceBilin.orthogonal Z).projection Z h (L X) =
      L ((matrixTraceBilin.orthogonal Z).projection Z h X) := by
  let W := matrixTraceBilin.orthogonal Z
  let P := W.projection Z h
  let Q := Z.projection W h.symm
  have hW {Y : Mat} (hY : Y ∈ W) : L Y ∈ W := by
    intro z hz
    rw [← hZ z hz, hB]
    exact hY z hz
  change P (L X) = L (P X)
  have he : L (P X) + L (Q X) = L X := by
    rw [← map_add, Submodule.projection_add_projection_eq_self]
  rw [← he, map_add,
    Submodule.projection_apply_of_mem_left h (hW (Submodule.projection_apply_mem h X)),
    hZ (Q X) (Submodule.projection_apply_mem h.symm X),
    (Submodule.projection_apply_eq_zero_iff h).mpr (Submodule.projection_apply_mem h.symm X),
    add_zero]

/-- If directions in `Z` commute with `C`, are trace-nondegenerate, and are
fixed by the centralizer and by the adjusted transpose, the conormal has
the same adjusted-transpose orbit-closure property as the centralizer. -/
theorem mem_closure_conormalConjugacy_of_adjustedTranspose
    {C A : Mat} {q : Matˣ} (hq : q.val * C * q.inv = Cᵀ) (Z : Submodule ℝ Mat)
    (hnd : (matrixTraceBilin.restrict Z).Nondegenerate)
    (hZC : ∀ z ∈ Z, Commute C z)
    (hZb : ∀ (b : Matˣ), Commute (b : Mat) C → ∀ z ∈ Z, b.val * z * b.inv = z)
    (hZq : ∀ z ∈ Z, q.inv * zᵀ * q.val = z)
    (hA : A ∈ matrixConormalWith C Z) :
    (A, q.inv * Aᵀ * q.val) ∈ closure {p : Mat × Mat | p.1 ∈ matrixConormalWith C Z ∧
      ∃ b : Matˣ, Commute (b : Mat) C ∧ b.val * p.1 * b.inv = p.2} := by
  let W := matrixTraceBilin.orthogonal Z
  have hcompl : IsCompl W Z :=
    (LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (fun X Y h => (matrixTraceBilin_isSymm.eq Y X).trans h) hnd).symm
  let P := W.projection Z hcompl
  let Q := Z.projection W hcompl.symm
  have hPA {X : Mat} (hX : Commute C X) : P X ∈ matrixConormalWith C Z := by
    have he : P X = X - Q X := eq_sub_of_add_eq (Submodule.projection_add_projection_eq_self hcompl X)
    exact mem_matrixConormalWith_iff.mpr ⟨he.symm ▸
      hX.sub_right (hZC (Q X) (Submodule.projection_apply_mem hcompl.symm X)),
      Submodule.projection_apply_mem hcompl X⟩
  let σ : Mat →ₗ[ℝ] Mat :=
    (LinearMap.mulLeftRight ℝ (q.inv, q.val)).comp
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap
  have hσ (X : Mat) : σ X = q.inv * Xᵀ * q.val := rfl
  have hσP (X : Mat) : P (σ X) = σ (P X) :=
    trace_orthogonal_projection_commutes Z hcompl σ
      (fun Y Y' => (matrixTraceBilin_units_conj q⁻¹ Yᵀ Y'ᵀ).trans (matrixTraceBilin_transpose Y Y'))
      hZq X
  have hPc (b : Matˣ) (hb : Commute (b : Mat) C) (X : Mat) :
      P (b.val * X * b.inv) = b.val * P X * b.inv :=
    trace_orthogonal_projection_commutes Z hcompl (LinearMap.mulLeftRight ℝ (b.val, b.inv))
      (matrixTraceBilin_units_conj b) (hZb b hb) X
  let F : Mat × Mat → Mat × Mat := fun p => (P p.1, P p.2)
  have hc : Continuous F :=
    (P.continuous_of_finiteDimensional.comp continuous_fst).prodMk
      (P.continuous_of_finiteDimensional.comp continuous_snd)
  obtain ⟨hAC, hAW⟩ := mem_matrixConormalWith_iff.mp hA
  have hlim := map_mem_closure hc (mem_closure_centralizerConjugacy_of_adjustedTranspose hq hAC)
    (t := {p : Mat × Mat | p.1 ∈ matrixConormalWith C Z ∧
      ∃ b : Matˣ, Commute (b : Mat) C ∧ b.val * p.1 * b.inv = p.2}) (by
      rintro ⟨X, Y⟩ ⟨hX, b, hb, he⟩
      exact ⟨hPA hX, b, hb, (hPc b hb X).symm.trans (congrArg P he)⟩)
  have hfixA : P A = A := Submodule.projection_apply_of_mem_left hcompl hAW
  change (P A, P (σ A)) ∈ _ at hlim
  rwa [hσP, hfixA, hσ] at hlim

private def conjugateAlgHom (b : Matˣ) : Mat →ₐ[ℝ] Mat where
  toFun X := b.val * X * b.inv
  map_one' := by simp
  map_mul' X Y := by simp [mul_assoc]
  map_zero' := by simp
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [← Algebra.commutes r b.val, mul_assoc, b.val_inv, mul_one]

private theorem conj_aeval (b : Matˣ) (C : Mat) (p : ℝ[X]) :
    b.val * aeval C p * b.inv = aeval (b.val * C * b.inv) p :=
  (Polynomial.aeval_algHom_apply (conjugateAlgHom b) C p).symm

private theorem conjugate_eq_of_commute {b : Matˣ} {C : Mat} (h : Commute (b : Mat) C) :
    b.val * C * b.inv = C := by
  rw [h.eq, mul_assoc, b.val_inv, mul_one]

private theorem conjugate_transpose_eq {q : Matˣ} {C : Mat}
    (hq : q.val * C * q.inv = Cᵀ) :
    q.inv * Cᵀ * q.val = C := by
  rw [← hq]
  simp [mul_assoc]

/-- Polynomial directions in the orbit base point are fixed by both of the
relevant actions, so they only need to be checked for trace nondegeneracy. -/
theorem mem_closure_conormalConjugacy_of_polynomialDirections
    {C A : Mat} {q : Matˣ} (hq : q.val * C * q.inv = Cᵀ) (Z : Submodule ℝ Mat)
    (hnd : (matrixTraceBilin.restrict Z).Nondegenerate)
    (hZ : Z ≤ (Algebra.adjoin ℝ {C}).toSubmodule) (hA : A ∈ matrixConormalWith C Z) :
    (A, q.inv * Aᵀ * q.val) ∈ closure {p : Mat × Mat | p.1 ∈ matrixConormalWith C Z ∧
      ∃ b : Matˣ, Commute (b : Mat) C ∧ b.val * p.1 * b.inv = p.2} := by
  have hp {z : Mat} (hz : z ∈ Z) : ∃ p : ℝ[X], aeval C p = z := by
    have h := hZ hz
    change z ∈ Algebra.adjoin ℝ {C} at h
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  apply mem_closure_conormalConjugacy_of_adjustedTranspose hq Z hnd _ _ _ hA
  · intro z hz
    obtain ⟨p, rfl⟩ := hp hz
    have h := (Commute.all X p).map (aeval C)
    rwa [aeval_X] at h
  · intro b hb z hz
    obtain ⟨p, rfl⟩ := hp hz
    rw [conj_aeval, conjugate_eq_of_commute hb]
  · intro z hz
    obtain ⟨p, rfl⟩ := hp hz
    rw [transpose_aeval_matrix]
    change q⁻¹.val * aeval Cᵀ p * q⁻¹.inv = aeval C p
    rw [conj_aeval]
    change aeval (q.inv * Cᵀ * q.val) p = aeval C p
    rw [conjugate_transpose_eq hq]

end Langlands
