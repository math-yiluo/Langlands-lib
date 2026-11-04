import Langlands.Group.FiniteChamberCartanCoverStatement
import Langlands.Algebra.FiniteChamberLatticeProof
import Langlands.Group.LeftQuotientInversion
import Mathlib.Tactic.Group

/-! # Orthant Cartan charts and empty-label compactness -/

namespace Langlands

open scoped BigOperators Pointwise

theorem finiteChamberCartanCover.{uΔ, uX, uG} :
    FiniteChamberCartanCoverStatement.{uΔ, uX, uG} := by
  intro Δ _ X _ G _ _ _ K hK e pair F₀ hF₀ hstd hcentral B hcover
  classical
  obtain ⟨gen, hgenpos, hgenzero, hgen⟩ := finiteChamberLattice Δ X pair hstd
  obtain ⟨R, hR, hrep⟩ := hgen B
  let T : Set G := (fun p : X × G => e (.ofAdd p.1) * p.2) '' (R ×ˢ F₀)
  have hT : T.Finite := (hR.prod hF₀).image _
  have hcharts (g : G) : ∃ n : Δ → ℕ, ∃ k₁ ∈ K, ∃ t ∈ T, ∃ k₂ ∈ K,
      ∃ z ∈ Subgroup.center G,
        g = k₁ * e (.ofAdd (∑ α, n α • gen α)) * t * k₂ * z := by
    obtain ⟨k₁, hk₁, x, f, hf, k₂, hk₂, hx, hg⟩ := hcover g
    obtain ⟨r, hr, n, z, hz, hxeq⟩ := hrep x hx
    have hzc := hcentral z hz
    have he : e (.ofAdd x) =
        e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α)) * e (.ofAdd z) := by
      rw [hxeq, ofAdd_add, ofAdd_add, map_mul, map_mul]
    have hrs : e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α)) =
        e (.ofAdd (∑ α, n α • gen α)) * e (.ofAdd r) := by
      rw [← e.map_mul, ← e.map_mul, mul_comm]
    refine ⟨n, k₁, hk₁, e (.ofAdd r) * f,
      ⟨(r, f), ⟨hr, hf⟩, rfl⟩, k₂, hk₂, e (.ofAdd z), hzc, ?_⟩
    calc
      g = k₁ * (e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α)) *
          e (.ofAdd z)) * f * k₂ := by rw [hg, he]
      _ = k₁ * (e (.ofAdd r) * e (.ofAdd (∑ α, n α • gen α))) *
          (e (.ofAdd z) * (f * k₂)) := by group
      _ = k₁ * (e (.ofAdd (∑ α, n α • gen α)) * e (.ofAdd r)) *
          ((f * k₂) * e (.ofAdd z)) := by
        rw [hrs, ← Subgroup.mem_center_iff.mp hzc (f * k₂)]
      _ = _ := by group
  refine ⟨gen, hgenpos, hgenzero, T, hT, hcharts, fun hEmpty => ?_⟩
  have : IsEmpty Δ := hEmpty
  apply Induction.compactSpace_quotient_of_compact_representatives
    (Subgroup.center G) ((hK.mul hT.isCompact).mul hK)
  intro g
  obtain ⟨n, k₁, hk₁, t, ht, k₂, hk₂, z, hz, hg⟩ := hcharts g
  refine ⟨k₁ * t * k₂, ⟨k₁ * t, ⟨k₁, hk₁, t, ht, rfl⟩, k₂, hk₂, rfl⟩,
    z, hz, ?_⟩
  simpa using hg

end Langlands
