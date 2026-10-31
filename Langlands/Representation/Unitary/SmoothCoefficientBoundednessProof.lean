import Langlands.Representation.Unitary.SmoothCoefficientBoundednessStatement
import Langlands.Representation.Unitary.HermitianDual

/-!
# Bounded smooth coefficients from an invariant positive form
-/

noncomputable section

namespace Langlands

universe uG uV

/-- An admissible unitarizable representation has bounded smooth-dual
coefficients, without a norm on its carrier in the statement. -/
theorem admissibleUnitarizableSmoothCoefficientsBounded
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    AdmissibleUnitarizableSmoothCoefficientsBounded G V := by
  rintro ρ hcofinal hρ ⟨b⟩ ℓ v
  obtain ⟨u, rfl⟩ := b.toSmoothDual_surjective hcofinal hρ ℓ
  let _ : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ b.toInnerProductCore
  let _ : InnerProductSpace ℂ V :=
    InnerProductSpace.ofCore b.toInnerProductCore.toCore
  refine ⟨‖u‖ * ‖v‖, mul_nonneg (norm_nonneg _) (norm_nonneg _), fun g => ?_⟩
  have hn : ‖ρ g v‖ = ‖v‖ := by
    change Real.sqrt (b.inner (ρ g v) (ρ g v)).re =
      Real.sqrt (b.inner v v).re
    rw [b.invariant]
  change ‖inner ℂ u (ρ g v)‖ ≤ ‖u‖ * ‖v‖
  calc
    ‖inner ℂ u (ρ g v)‖ ≤ ‖u‖ * ‖ρ g v‖ := norm_inner_le_norm u (ρ g v)
    _ = ‖u‖ * ‖v‖ := by rw [hn]

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- Convenient form of boundedness with the unitarizability hypothesis first. -/
theorem IsUnitarizable.smoothCoefficient_bounded (hunitary : IsUnitarizable ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (ℓ : SmoothDual ρ) (v : V) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : G, ‖smoothDualPairing ρ ℓ (ρ g v)‖ ≤ C :=
  admissibleUnitarizableSmoothCoefficientsBounded G V ρ hcofinal hρ hunitary ℓ v

/-- A single unbounded smooth-dual coefficient obstructs unitarizability. -/
theorem not_isUnitarizable_of_unbounded_smoothCoefficient
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (ℓ : SmoothDual ρ) (v : V)
    (hunbounded : ∀ C : ℝ, ∃ g : G,
      C < ‖smoothDualPairing ρ ℓ (ρ g v)‖) :
    ¬ IsUnitarizable ρ := by
  intro hunitary
  obtain ⟨C, _, hC⟩ := hunitary.smoothCoefficient_bounded hcofinal hρ ℓ v
  obtain ⟨g, hg⟩ := hunbounded C
  exact (not_lt_of_ge (hC g)) hg

/-- An unbounded sequence of values of one smooth coefficient also obstructs
unitarizability; no topological assumption on the sequence is needed. -/
theorem not_isUnitarizable_of_unbounded_smoothCoefficient_sequence
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (ℓ : SmoothDual ρ) (v : V) (g : ℕ → G)
    (hunbounded : ∀ C : ℝ, ∃ n : ℕ,
      C < ‖smoothDualPairing ρ ℓ (ρ (g n) v)‖) :
    ¬ IsUnitarizable ρ := by
  apply not_isUnitarizable_of_unbounded_smoothCoefficient hcofinal hρ ℓ v
  intro C
  obtain ⟨n, hn⟩ := hunbounded C
  exact ⟨g n, hn⟩

end Langlands
