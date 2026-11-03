import Langlands.Representation.Aubert.General.JacquetAdmissibility
import Langlands.Representation.Exponents.Central
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Algebra.BigOperators.Pi

/-! # Coefficient decay relative to actual inverse Haar modulus weights -/

open scoped NNReal

namespace Langlands

universe uG uV uI

/-- Actual strict normalized Jacquet spectra on each lattice ray give
product exponential coefficient bounds whose squares dominate the actual
inverse Haar modulus weights. Geometric contraction data stay explicit. -/
def HaarNormalizedLatticeCoefficientBoundStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    [NonarchimedeanGroup G] (I : Type uI) [Fintype I] [DecidableEq I]
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N₀ M₀ Nbar₀ : Subgroup G),
    (∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar₀, ∃ m ∈ K.toSubgroup ⊓ M₀,
      ∃ u ∈ K.toSubgroup ⊓ N₀, k = l * m * u) →
    ∀ τ : Multiplicative (I → ℕ) →* G,
      (∀ n u, u ∈ K.toSubgroup ⊓ N₀ →
        τ (.ofAdd n) * u * (τ (.ofAdd n))⁻¹ ∈ K) →
      (∀ n l, l ∈ K.toSubgroup ⊓ Nbar₀ →
        (τ (.ofAdd n))⁻¹ * l * τ (.ofAdd n) ∈ K) →
      (∀ n m, m ∈ K.toSubgroup ⊓ M₀ →
        (τ (.ofAdd n))⁻¹ * m * τ (.ofAdd n) ∈ K) →
      ∀ (N M Nbar : I → Subgroup G)
        (hN : ∀ i, IsClosed (N i : Set G))
        (hMN : ∀ i, M i ≤ Subgroup.normalizer (N i)),
        (∀ i, Jacquet.HasIwahoriContractionBasis (N i) (M i) (Nbar i)) →
        ∀ z : ∀ i, Subgroup.center (M i),
          (∀ i, τ (.ofAdd (Pi.single i 1)) = ((z i : M i) : G)) →
          (∀ i, Jacquet.IsIwahoriContraction K (N i) (M i) (Nbar i) ((z i : M i) : G)) →
          (∀ i (χ : Subgroup.center (M i) →* ℂˣ),
            IsCentralExponent
              ((Aubert.General.normalizedJacquetFunctor (N i) (M i) (hN i) (hMN i)).obj A).representation χ →
            ‖(χ (z i) : ℂ)‖ < 1) →
          ∀ (v : fixedVectors A.representation K.toSubgroup) (φ : Module.Dual ℂ A),
            φ ∈ fixedVectors A.representation.dual K.toSubgroup →
            ∃ a : I → ℝ, (∀ i, 0 < a i ∧
              a i ^ 2 * (((HaarModulus.closedRestrictCharacter (N i) (hN i) (M i) (hMN i)
                (z i : M i) : ℝ≥0) : ℝ))⁻¹ < 1) ∧
              ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ,
                ‖φ (A.representation (τ (.ofAdd n)) (v : A))‖ ≤ C * ∏ i, a i ^ n i

end Langlands
