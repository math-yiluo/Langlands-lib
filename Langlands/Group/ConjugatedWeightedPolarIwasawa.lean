import Langlands.Group.WeightedPolarIwasawa

/-! # Weighted covering without a simultaneous self-adjoint diagonalization -/

noncomputable section

universe u v

open Filter
open scoped Topology Pointwise Matrix

namespace Langlands.Group.WeightedPolarIwasawa

open Langlands.GroupScheme.GeneralLinear

variable {𝕜 : Type u} [RCLike 𝕜]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {A : Type v} [Group A]

/-- Change the coefficient basis of a representation by an arbitrary matrix unit. -/
def conjugatedRepresentation (ρ : A →* GL n 𝕜) (B : GL n 𝕜) : A →* GL n 𝕜 where
  toFun g := B⁻¹ * ρ g * B
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

@[simp] theorem conjugatedRepresentation_apply
    (ρ : A →* GL n 𝕜) (B : GL n 𝕜) (g : A) :
    conjugatedRepresentation ρ B g = B⁻¹ * ρ g * B := rfl

variable [TopologicalSpace A]

/-- Compact extraction for the congruence transform of a right remainder.
The conjugating matrix need not be unitary. -/
theorem exists_congruence_block_remainder
    (ρ : A →* GL n 𝕜) (hρ : Continuous ρ)
    (hstar : ∀ q ∈ ρ.range, star q ∈ ρ.range)
    (K : Subgroup A) (hK : IsCompact (K : Set A))
    (hh : ∀ x : A, ∃ k ∈ K, (ρ (x * k⁻¹) : Matrix n n 𝕜).IsHermitian)
    (B : GL n 𝕜) (w : n → ℤ)
    (t : ℕ → ℝ) (ht0 : ∀ m, t m ≠ 0) (ht : Tendsto t atTop (𝓝 0))
    (D : ℕ → A)
    (hD : ∀ m, (B⁻¹ * ρ (D m) * B : Matrix n n 𝕜) =
      Matrix.diagonal (fun i => (t m : 𝕜) ^ w i)) (g : A) :
    ∃ k ∈ K, star B * ρ (g * k⁻¹) * B ∈ blockParabolicSubgroup 𝕜 w := by
  classical
  let : FirstCountableTopology (Matrix n n 𝕜) :=
    inferInstanceAs (FirstCountableTopology (n → n → 𝕜))
  let : FirstCountableTopology (Matrix n n 𝕜)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  let : FirstCountableTopology (GL n 𝕜) :=
    Units.isInducing_embedProduct.firstCountableTopology
  choose E hE using fun m => hstar (ρ (D m)) ⟨D m, rfl⟩
  choose k hkK hkH using fun m => hh (E m * g)
  obtain ⟨q, hq, φ, hφ, hlim⟩ :=
    (hK.image hρ).tendsto_subseq (x := fun m => ρ (k m))
      (fun m => ⟨k m, hkK m, rfl⟩)
  obtain ⟨k₀, hk₀, rfl⟩ := hq
  have hb :
      Tendsto (fun m => (star B * (ρ g * (ρ (k (φ m)))⁻¹) * B : Matrix n n 𝕜))
        atTop (𝓝 (star B * (ρ g * (ρ k₀)⁻¹) * B : Matrix n n 𝕜)) :=
    Units.continuous_val.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul (tendsto_const_nhds.mul hlim.inv)).mul
        tendsto_const_nhds)
  have hh' (m : ℕ) :
      (Matrix.diagonal (fun i => (t (φ m) : 𝕜) ^ w i) *
        (star B * (ρ g * (ρ (k (φ m)))⁻¹) * B : Matrix n n 𝕜)).IsHermitian := by
    have hsa : star (B⁻¹ * ρ (D (φ m)) * B) = B⁻¹ * ρ (D (φ m)) * B := by
      apply Units.ext
      change (B⁻¹ * ρ (D (φ m)) * B : Matrix n n 𝕜)ᴴ = _
      simp only [Units.val_mul, hD]
      apply Matrix.isHermitian_diagonal_iff.mpr
      intro i
      simp [IsSelfAdjoint, RCLike.star_def]
    have hc : star B * star (ρ (D (φ m))) =
        (B⁻¹ * ρ (D (φ m)) * B) * star B := by
      calc
        star B * star (ρ (D (φ m))) =
            star (B⁻¹ * ρ (D (φ m)) * B) * star B := by
              simp [star_mul, mul_assoc]
        _ = _ := by rw [hsa]
    have hp :
        star B * ρ (E (φ m) * g * (k (φ m))⁻¹) * B =
          (B⁻¹ * ρ (D (φ m)) * B) *
            (star B * (ρ g * (ρ (k (φ m)))⁻¹) * B) := by
      simp only [map_mul, map_inv, hE]
      calc
        star B * (star (ρ (D (φ m))) * ρ g * (ρ (k (φ m)))⁻¹) * B =
            (star B * star (ρ (D (φ m)))) *
              (ρ g * (ρ (k (φ m)))⁻¹) * B := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]
    have h := Matrix.isHermitian_conjTranspose_mul_mul (B : Matrix n n 𝕜) (hkH (φ m))
    change (star B * ρ (E (φ m) * g * (k (φ m))⁻¹) * B :
      Matrix n n 𝕜).IsHermitian at h
    have hp' := congrArg (fun q : GL n 𝕜 => (q : Matrix n n 𝕜)) hp
    simp only [Units.val_mul] at hp'
    rw [hp', hD] at h
    exact h
  refine ⟨k₀, hk₀, ?_⟩
  rw [mem_blockParabolicSubgroup]
  intro i j hij
  simpa only [map_mul, map_inv, Units.val_mul] using
    limit_entry_eq_zero w (t ∘ φ) (fun m => ht0 (φ m))
      (ht.comp hφ.tendsto_atTop) _ _ hb hh' i j hij

/-- Two congruence limits cancel the change of basis. Thus the weighted
parabolic covers with the original compact subgroup even when the diagonalizing
basis does not preserve adjoints. -/
theorem conjugated_mul_compact_eq_univ_of_hermitian
    (ρ : A →* GL n 𝕜) (hρ : Continuous ρ)
    (hstar : ∀ q ∈ ρ.range, star q ∈ ρ.range)
    (K : Subgroup A) (hK : IsCompact (K : Set A))
    (hh : ∀ x : A, ∃ k ∈ K, (ρ (x * k⁻¹) : Matrix n n 𝕜).IsHermitian)
    (B : GL n 𝕜) (w : n → ℤ)
    (t : ℕ → ℝ) (ht0 : ∀ m, t m ≠ 0) (ht : Tendsto t atTop (𝓝 0))
    (D : ℕ → A)
    (hD : ∀ m, (B⁻¹ * ρ (D m) * B : Matrix n n 𝕜) =
      Matrix.diagonal (fun i => (t m : 𝕜) ^ w i)) :
    (weightedParabolicSubgroup (conjugatedRepresentation ρ B) w : Set A) *
      (K : Set A) = Set.univ := by
  obtain ⟨k₀, hk₀, h₀⟩ :=
    exists_congruence_block_remainder ρ hρ hstar K hK hh B w t ht0 ht D hD 1
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨k, hk, h⟩ :=
    exists_congruence_block_remainder ρ hρ hstar K hK hh B w t ht0 ht D hD (k₀⁻¹ * g)
  have hp : g * k⁻¹ ∈ weightedParabolicSubgroup (conjugatedRepresentation ρ B) w := by
    change B⁻¹ * ρ (g * k⁻¹) * B ∈ blockParabolicSubgroup 𝕜 w
    have hmem := (blockParabolicSubgroup 𝕜 w).mul_mem
      ((blockParabolicSubgroup 𝕜 w).inv_mem h₀) h
    convert hmem using 1
    simp [map_mul, map_inv, mul_assoc]
  exact Set.mem_mul.mpr ⟨g * k⁻¹, hp, k, hk, inv_mul_cancel_right g k⟩

end Langlands.Group.WeightedPolarIwasawa
