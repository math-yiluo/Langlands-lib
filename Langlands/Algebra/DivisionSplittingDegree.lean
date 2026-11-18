import Langlands.Algebra.CentralSimpleScalarExtension
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! # Divisibility of the degree of an actual division-algebra splitting field -/

noncomputable section
universe u v w
open scoped TensorProduct Matrix.Module

namespace Langlands.CentralSimple

variable {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
  [FiniteDimensional k D] {L : Type w} [Field L] [Algebra k L] [FiniteDimensional k L]

/-- The actual size of a division-algebra matrix splitting divides its field degree. -/
theorem division_splitting_size_dvd_field_degree {n : ℕ} (hn : 0 < n)
    (e : L ⊗[k] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    n ∣ Module.finrank k L := by
  let ρ : D →ₐ[k] Matrix (Fin n) (Fin n) L :=
    (e.restrictScalars k).toAlgHom.comp Algebra.TensorProduct.includeRight
  let V := Fin n → L
  let : Module D V := Module.compHom V ρ.toRingHom
  have : IsScalarTower k D V := ⟨fun a d v => by
      change ρ (a • d) • v = a • (ρ d • v)
      rw [map_smul, smul_assoc]⟩
  have hdvd := Module.finrank_dvd_finrank_right k D V
  have hdimD : Module.finrank k D = n * n := finrank_eq_matrix_size k D L n e
  have hdimV : Module.finrank k V = n * Module.finrank k L := by
    rw [← Module.finrank_mul_finrank k L V]
    simp only [V, Module.finrank_pi, Fintype.card_fin]
    exact Nat.mul_comm _ _
  rw [hdimD, hdimV] at hdvd
  exact (Nat.mul_dvd_mul_iff_left hn).mp hdvd

/-- A degree-six division algebra admits no actual matrix splitting over a finite
odd-degree field extension. -/
theorem division_degree_six_not_split_over_odd_extension
    (hdim : Module.finrank k D = 36) (hodd : Odd (Module.finrank k L))
    (n : ℕ) (hn : 0 < n) :
    ¬ Nonempty (L ⊗[k] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  rintro ⟨e⟩
  have hn6 : n = 6 := by
    have hsize := finrank_eq_matrix_size k D L n e
    rw [hdim] at hsize
    nlinarith
  have h6 := division_splitting_size_dvd_field_degree hn e
  rw [hn6] at h6
  have h2 : 2 ∣ Module.finrank k L := dvd_trans (by decide : 2 ∣ 6) h6
  obtain ⟨a, ha⟩ := hodd
  omega

end Langlands.CentralSimple
