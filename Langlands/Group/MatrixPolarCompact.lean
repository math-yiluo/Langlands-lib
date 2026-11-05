import Langlands.Global.ArchimedeanCompact
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Order.Compact

/-! # The compact subgroup of a polar matrix realization -/

noncomputable section

universe u v

namespace Langlands.Group.MatrixPolarCompact

open Matrix
open scoped ComplexOrder

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}

private theorem eigenvalue_norm_le_one
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜))
    (hL : IsCompact (L : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)))
    (g : Matrix.GeneralLinearGroup (Fin n) 𝕜) (hg : g ∈ L)
    (x : Fin n → 𝕜) (hx : x ≠ 0) (r : ℝ)
    (heigen : (g : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x = r • x) :
    |r| ≤ 1 := by
  have hc : Continuous (fun a : Matrix.GeneralLinearGroup (Fin n) 𝕜 =>
      ‖(a : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖) :=
    (Units.continuous_val.matrix_mulVec continuous_const).norm
  obtain ⟨a, ha, hmax⟩ := hL.exists_isMaxOn ⟨1, L.one_mem⟩ hc.continuousOn
  have hpos : 0 < ‖(a : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖ := by
    have hle : ‖x‖ ≤ ‖(a : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖ := by
      have hle := hmax L.one_mem
      change ‖((1 : Matrix.GeneralLinearGroup (Fin n) 𝕜) :
        Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖ ≤ _ at hle
      simpa only [Units.val_one, Matrix.one_mulVec] using hle
    exact (norm_pos_iff.mpr hx).trans_le hle
  have hm := hmax (L.mul_mem ha hg)
  have haction :
      ((a * g : Matrix.GeneralLinearGroup (Fin n) 𝕜) :
          Matrix (Fin n) (Fin n) 𝕜) *ᵥ x =
        r • ((a : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul]
  change ‖_‖ ≤ ‖(a : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x‖ at hm
  rw [haction, norm_smul, Real.norm_eq_abs] at hm
  nlinarith

/-- Every real eigenvalue on a nonzero vector of an element of a compact matrix
subgroup has absolute value one. -/
theorem eigenvalue_abs_eq_one
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜))
    (hL : IsCompact (L : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)))
    (g : Matrix.GeneralLinearGroup (Fin n) 𝕜) (hg : g ∈ L)
    (x : Fin n → 𝕜) (hx : x ≠ 0) (r : ℝ)
    (heigen : (g : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x = r • x) :
    |r| = 1 := by
  have hr : r ≠ 0 := by
    intro hr
    have hz : (g : Matrix (Fin n) (Fin n) 𝕜) *ᵥ x = 0 := by
      simpa [hr] using heigen
    have heq := congrArg
      (fun y => (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜).val *ᵥ y) hz
    apply hx
    simpa only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using heq
  have hinv : (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜).val *ᵥ x = r⁻¹ • x := by
    have heq := congrArg
      (fun y => (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜).val *ᵥ y) heigen
    have heq' : x = r • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜).val *ᵥ x) := by
      simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec, Matrix.mulVec_smul] using heq
    calc
      (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜).val *ᵥ x =
          r⁻¹ • (r • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) 𝕜).val *ᵥ x)) :=
        (inv_smul_smul₀ hr _).symm
      _ = r⁻¹ • x := congrArg (r⁻¹ • ·) heq'.symm
  have hle := eigenvalue_norm_le_one L hL g hg x hx r heigen
  have hge := eigenvalue_norm_le_one L hL g⁻¹ (L.inv_mem hg) x hx r⁻¹ hinv
  rw [abs_inv] at hge
  have habs : 0 < |r| := abs_pos.mpr hr
  exact le_antisymm hle ((inv_le_one₀ habs).mp hge)

/-- A positive semidefinite matrix in a compact subgroup of matrix units is the
identity. No containment of a full unitary group is needed. -/
theorem eq_one_of_posSemidef
    (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜))
    (hL : IsCompact (L : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)))
    (g : Matrix.GeneralLinearGroup (Fin n) 𝕜) (hg : g ∈ L)
    (hpos : (g : Matrix (Fin n) (Fin n) 𝕜).PosSemidef) :
    g = 1 := by
  have heigen : hpos.isHermitian.eigenvalues = fun _ => 1 := by
    funext i
    have hnorm := eigenvalue_abs_eq_one L hL g hg
      (⇑(hpos.isHermitian.eigenvectorBasis i))
      (by
        intro hz
        exact hpos.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
          ((WithLp.ofLp_eq_zero 2).mp hz))
      (hpos.isHermitian.eigenvalues i)
      (hpos.isHermitian.mulVec_eigenvectorBasis i)
    rwa [abs_of_nonneg (hpos.eigenvalues_nonneg i)] at hnorm
  apply Units.ext
  rw [hpos.isHermitian.spectral_theorem, heigen]
  simp [Function.comp_def]

variable {A : Type v} [Group A]

/-- The inverse image of the standard unitary group under a matrix realization. -/
def unitarySubgroup
    (ρ : A →* Matrix.GeneralLinearGroup (Fin n) 𝕜) : Subgroup A :=
  (Unitary.toUnits (R := Matrix (Fin n) (Fin n) 𝕜)).range.comap ρ

/-- Unitary membership is the literal matrix condition. -/
theorem mem_unitarySubgroup
    (ρ : A →* Matrix.GeneralLinearGroup (Fin n) 𝕜) (g : A) :
    g ∈ unitarySubgroup ρ ↔
      (ρ g : Matrix (Fin n) (Fin n) 𝕜) ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    exact q.property
  · intro hg
    refine ⟨⟨(ρ g : Matrix (Fin n) (Fin n) 𝕜), hg⟩, ?_⟩
    exact Units.ext rfl

variable [TopologicalSpace A]

/-- Polar factors inside the original group suffice for compact-overgroup
maximality of its unitary subgroup. This does not construct such factors. -/
theorem compact_overgroup_eq
    (ρ : A →* Matrix.GeneralLinearGroup (Fin n) 𝕜)
    (hρcont : Continuous ρ) (hρinj : Function.Injective ρ)
    (hpolar : ∀ g : A, ∃ k a : A,
      k ∈ unitarySubgroup ρ ∧
      (ρ a : Matrix (Fin n) (Fin n) 𝕜).PosSemidef ∧ g = k * a)
    (L : Subgroup A) (hL : IsCompact (L : Set A))
    (hcontains : unitarySubgroup ρ ≤ L) :
    L = unitarySubgroup ρ := by
  apply le_antisymm _ hcontains
  intro g hg
  obtain ⟨k, a, hk, ha, hka⟩ := hpolar g
  have haL : a ∈ L := by
    have := L.mul_mem (L.inv_mem (hcontains hk)) hg
    simpa only [hka, inv_mul_cancel_left] using this
  have hcompact : IsCompact (L.map ρ : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)) := by
    exact hL.image hρcont
  have haone : a = 1 := by
    apply hρinj
    simpa only [map_one] using
      eq_one_of_posSemidef (L.map ρ) hcompact (ρ a) ⟨a, haL, rfl⟩ ha
  simpa only [hka, haone, mul_one] using hk

end Langlands.Group.MatrixPolarCompact
