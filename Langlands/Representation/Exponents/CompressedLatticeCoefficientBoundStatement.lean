import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Algebra.BigOperators.Pi

/-! # Coefficient bounds on a finite lattice of actual compressed operators -/

namespace Langlands

universe uG uV uI

/-- A finite lattice whose actual compact compression is multiplicative and has
strictly bounded generator eigenvalues has a product exponential coefficient
bound. The factorization and conjugation conditions are explicit. -/
def CompressedLatticeCoefficientBoundStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (I : Type uI) [Fintype I] [DecidableEq I]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G),
    (∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u) →
    ∀ τ : Multiplicative (I → ℕ) →* G,
      (∀ n u, u ∈ K.toSubgroup ⊓ N →
        τ (.ofAdd n) * u * (τ (.ofAdd n))⁻¹ ∈ K) →
      (∀ n l, l ∈ K.toSubgroup ⊓ Nbar →
        (τ (.ofAdd n))⁻¹ * l * τ (.ofAdd n) ∈ K) →
      (∀ n m, m ∈ K.toSubgroup ⊓ M →
        (τ (.ofAdd n))⁻¹ * m * τ (.ofAdd n) ∈ K) →
      ∀ s : I → ℝ, (∀ i, 0 < s i) →
        (∀ i (μ : ℂ) (x : fixedVectors ρ K.toSubgroup), x ≠ 0 →
          Jacquet.compressedAction ρ hρ.1 K hK (τ (.ofAdd (Pi.single i 1))) x = μ • x →
          ‖μ‖ < s i) →
        ∀ (v : fixedVectors ρ K.toSubgroup) (φ : Module.Dual ℂ V),
          φ ∈ fixedVectors ρ.dual K.toSubgroup →
          ∃ a : I → ℝ, (∀ i, 0 < a i ∧ a i < s i) ∧
            ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ,
              ‖φ (ρ (τ (.ofAdd n)) (v : V))‖ ≤ C * ∏ i, a i ^ n i

end Langlands
