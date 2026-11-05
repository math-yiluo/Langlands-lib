import Langlands.GroupScheme.Dynamic.GeneralLinear
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Sequences

/-! # Weighted parabolic coverage from Hermitian remainders -/

noncomputable section

universe u v

open Filter
open scoped Topology Pointwise

namespace Langlands.Group.WeightedPolarIwasawa

variable {𝕜 : Type u} [RCLike 𝕜]
variable {n : Type} [Fintype n] [DecidableEq n]

/-- A limit of matrices whose weighted left multiples are Hermitian has no
entries from a smaller row weight to a larger column weight. -/
theorem limit_entry_eq_zero
    (w : n → ℤ) (t : ℕ → ℝ) (ht0 : ∀ m, t m ≠ 0)
    (ht : Tendsto t atTop (𝓝 0))
    (b : ℕ → Matrix n n 𝕜) (B : Matrix n n 𝕜)
    (hb : Tendsto b atTop (𝓝 B))
    (hh : ∀ m, (Matrix.diagonal (fun i => (t m : 𝕜) ^ w i) * b m).IsHermitian)
    (i j : n) (hij : w i < w j) :
    B i j = 0 := by
  have heq (m : ℕ) :
      b m i j = (t m : 𝕜) ^ (w j - w i) * star (b m j i) := by
    have h := (hh m).apply i j
    simp only [Matrix.diagonal_mul, star_mul, star_zpow₀,
      RCLike.star_def, RCLike.conj_ofReal] at h
    have hn : (t m : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (ht0 m)
    rw [zpow_sub₀ hn]
    apply (mul_left_cancel₀ (zpow_ne_zero _ hn))
    calc
      (t m : 𝕜) ^ w i * b m i j =
          star (b m j i) * (t m : 𝕜) ^ w j := h.symm
      _ = (t m : 𝕜) ^ w i *
          ((t m : 𝕜) ^ w j / (t m : 𝕜) ^ w i * star (b m j i)) := by
        field_simp
  have hpow : Tendsto (fun m => (t m : 𝕜) ^ (w j - w i)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m => (t m : 𝕜)) atTop (𝓝 0) := by
      convert ((RCLike.continuous_ofReal (K := 𝕜)).tendsto (0 : ℝ)).comp ht using 1
      · rfl
      · congr 1
        exact RCLike.ofReal_zero.symm
    simpa [zero_zpow (w j - w i) (sub_pos.mpr hij).ne'] using
      hcast.zpow₀ (w j - w i) (Or.inr (sub_nonneg.mpr hij.le))
  have hji : Tendsto (fun m => star (b m j i)) atTop (𝓝 (star (B j i))) :=
    (continuous_star.continuousAt.tendsto).comp
      ((continuous_apply_apply j i).continuousAt.tendsto.comp hb)
  have hz : Tendsto (fun m => b m i j) atTop (𝓝 0) := by
    simpa only [← heq, zero_mul] using hpow.mul hji
  exact tendsto_nhds_unique
    ((continuous_apply_apply i j).continuousAt.tendsto.comp hb) hz

variable {A : Type v} [Group A] [TopologicalSpace A]

/-- The inverse image of the matrix subgroup with vanishing entries from a
smaller row weight to a larger column weight. -/
def weightedParabolicSubgroup (ρ : A →* GL n 𝕜) (w : n → ℤ) : Subgroup A :=
  (Langlands.GroupScheme.GeneralLinear.blockParabolicSubgroup 𝕜 w).comap ρ

/-- A compact subgroup with Hermitian right remainders covers the group together
with a weighted parabolic, provided a sequence of the diagonal weight matrices
lies in the represented group. -/
theorem mul_compact_eq_univ_of_hermitian
    (ρ : A →* GL n 𝕜) (hρ : Continuous ρ)
    (K : Subgroup A) (hK : IsCompact (K : Set A))
    (hh : ∀ x : A, ∃ k ∈ K, (ρ (x * k⁻¹) : Matrix n n 𝕜).IsHermitian)
    (w : n → ℤ) (t : ℕ → ℝ) (ht0 : ∀ m, t m ≠ 0)
    (ht : Tendsto t atTop (𝓝 0)) (D : ℕ → A)
    (hD : ∀ m, (ρ (D m) : Matrix n n 𝕜) =
      Matrix.diagonal (fun i => (t m : 𝕜) ^ w i)) :
    (weightedParabolicSubgroup ρ w : Set A) * (K : Set A) = Set.univ := by
  classical
  let : FirstCountableTopology (Matrix n n 𝕜) :=
    inferInstanceAs (FirstCountableTopology (n → n → 𝕜))
  let : FirstCountableTopology (Matrix n n 𝕜)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  let : FirstCountableTopology (GL n 𝕜) :=
    Units.isInducing_embedProduct.firstCountableTopology
  apply Set.eq_univ_of_forall
  intro g
  choose k hkK hkH using fun m => hh (D m * g)
  obtain ⟨q, hq, φ, hφ, hlim⟩ :=
    (hK.image hρ).tendsto_subseq (x := fun m => ρ (k m))
      (fun m => ⟨k m, hkK m, rfl⟩)
  obtain ⟨k₀, hk₀, rfl⟩ := hq
  have hb :
      Tendsto (fun m => (ρ g * (ρ (k (φ m)))⁻¹ : Matrix n n 𝕜))
        atTop (𝓝 (ρ g * (ρ k₀)⁻¹ : Matrix n n 𝕜)) :=
    Units.continuous_val.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hlim.inv)
  have hh' (m : ℕ) :
      (Matrix.diagonal (fun i => (t (φ m) : 𝕜) ^ w i) *
        (ρ g * (ρ (k (φ m)))⁻¹ : Matrix n n 𝕜)).IsHermitian := by
    simpa only [map_mul, map_inv, Units.val_mul, hD, mul_assoc] using hkH (φ m)
  have hp : g * k₀⁻¹ ∈ weightedParabolicSubgroup ρ w := by
    change ρ (g * k₀⁻¹) ∈
      Langlands.GroupScheme.GeneralLinear.blockParabolicSubgroup 𝕜 w
    rw [Langlands.GroupScheme.GeneralLinear.mem_blockParabolicSubgroup]
    intro i j hij
    simpa only [map_mul, map_inv, Units.val_mul] using
      limit_entry_eq_zero w (t ∘ φ) (fun m => ht0 (φ m))
        (ht.comp hφ.tendsto_atTop) _ _ hb hh' i j hij
  exact Set.mem_mul.mpr ⟨g * k₀⁻¹, hp, k₀, hk₀, inv_mul_cancel_right g k₀⟩

end Langlands.Group.WeightedPolarIwasawa
