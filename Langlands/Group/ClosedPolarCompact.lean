import Langlands.Group.MatrixPolarCompact

/-! # Maximal compact subgroups from closed polar matrix realizations -/

noncomputable section

universe u v

namespace Langlands.Group.MatrixPolarCompact

open scoped ComplexOrder

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}
variable {A : Type v} [Group A] [TopologicalSpace A]

/-- The unitary subgroup of a closed matrix realization is compact. -/
theorem isCompact_unitarySubgroup
    (ρ : A →* Matrix.GeneralLinearGroup (Fin n) 𝕜)
    (hρ : Topology.IsClosedEmbedding ρ) :
    IsCompact (unitarySubgroup ρ : Set A) := by
  have hu : Continuous (Unitary.toUnits (R := Matrix (Fin n) (Fin n) 𝕜)) := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_subtype_val.comp continuous_inv⟩
  exact hρ.isCompact_preimage (isCompact_range hu)

/-- Construct a maximal compact subgroup from a faithful closed realization
and polar factors inside the original group. -/
def maximalCompactOfClosedPolar
    (ρ : A →* Matrix.GeneralLinearGroup (Fin n) 𝕜)
    (hρ : Topology.IsClosedEmbedding ρ)
    (hpolar : ∀ g : A, ∃ k a : A,
      k ∈ unitarySubgroup ρ ∧
      (ρ a : Matrix (Fin n) (Fin n) 𝕜).PosSemidef ∧ g = k * a) :
    {K : Subgroup A // IsCompact (K : Set A) ∧
      ∀ L : Subgroup A, IsCompact (L : Set A) → K ≤ L → L = K} :=
  ⟨unitarySubgroup ρ, isCompact_unitarySubgroup ρ hρ,
    compact_overgroup_eq ρ hρ.continuous hρ.injective hpolar⟩

end Langlands.Group.MatrixPolarCompact
