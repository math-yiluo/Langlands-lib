import Langlands.BushnellKutzko.TypeJacquetCompression

/-! # Compact averages computed through a homomorphism onto a finite group -/

noncomputable section

namespace Langlands.Jacquet

universe uG uV uQ

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Let `θ` be a homomorphism from a compact open subgroup `H` onto a finite group `Q`, with a
section `t`. The average over `H` of a vector fixed by the kernel of `θ` is the mean of its
translates by the section. -/
theorem averageMap_eq_mean_of_hom (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (H : OpenSubgroup G) (hH : IsCompact (H : Set G)) {Q : Type uQ} [Group Q] [Fintype Q]
    (θ : H.toSubgroup →* Q) (t : Q → G) (ht : ∀ q, t q ∈ H)
    (hθt : ∀ q, θ ⟨t q, ht q⟩ = q) (w : V)
    (hw : ∀ h : H.toSubgroup, θ h = 1 → ρ h w = w) :
    Compact.averageMap ρ hρ H hH w = (Fintype.card Q : ℂ)⁻¹ • ∑ q, ρ (t q) w := by
  set x := (Fintype.card Q : ℂ)⁻¹ • ∑ q, ρ (t q) w with hx
  have hfix : x ∈ fixedVectors ρ H.toSubgroup := by
    intro k
    change ρ k x = x
    rw [hx, map_smul, map_sum]
    congr 1
    have hstep : ∀ q, ρ k (ρ (t q) w) = ρ (t (θ k * q)) w := by
      intro q
      let l : H.toSubgroup := (⟨t (θ k * q), ht _⟩ : H.toSubgroup)⁻¹ * k * ⟨t q, ht q⟩
      have hl : θ l = 1 := by
        simp only [l, map_mul, map_inv, hθt]
        group
      have hlw := hw l hl
      calc ρ k (ρ (t q) w) = ρ ((k : G) * t q) w := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (t (θ k * q) * (l : G)) w := by
          congr 2
          simp only [l, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        _ = ρ (t (θ k * q)) w := by rw [map_mul, Module.End.mul_apply, hlw]
    simp only [hstep]
    exact Equiv.sum_comp (Equiv.mulLeft (θ k)) (fun q => ρ (t q) w)
  have havg : Compact.averageMap ρ hρ H hH x = Compact.averageMap ρ hρ H hH w := by
    rw [hx, map_smul, map_sum]
    simp only [averageMap_apply_of_mem ρ hρ H hH (ht _), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]
  rw [← havg, Compact.averageMap_id ρ hρ H hH x hfix]

end Langlands.Jacquet
