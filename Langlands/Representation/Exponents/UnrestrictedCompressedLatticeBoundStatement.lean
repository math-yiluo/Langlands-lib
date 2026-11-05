import Langlands.Representation.Exponents.CompressedLatticeCoefficientBoundStatement

/-! # Unrestricted exponential growth on compressed lattices -/

namespace Langlands

universe uG uV uI

/-- A finite multiplicative lattice of actual compact compressions has an
exponential coefficient bound, without a hypothesis on its eigenvalues. The
radii depend only on the representation, the subgroup and the lattice. -/
def UnrestrictedCompressedLatticeBoundStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (I : Type uI) [Fintype I] [DecidableEq I]
    (ρ : Representation ℂ G V) (_hρ : IsAdmissible ρ)
    (K : OpenSubgroup G) (_hK : IsCompact (K : Set G))
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
      ∃ a : I → ℝ, (∀ i, 1 < a i) ∧
        ∀ (v : fixedVectors ρ K.toSubgroup) (φ : Module.Dual ℂ V),
          φ ∈ fixedVectors ρ.dual K.toSubgroup →
          ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ,
            ‖φ (ρ (τ (.ofAdd n)) (v : V))‖ ≤ C * ∏ i, a i ^ n i

end Langlands
