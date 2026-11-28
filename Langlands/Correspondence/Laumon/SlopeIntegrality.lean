import Langlands.Correspondence.Laumon.Slopes

/-!
# Integrality of ℓ-adic slopes
-/

noncomputable section

open ValuativeRel
open Langlands.Ramification.Local (localAbsoluteUpperRamificationGroup localWildInertia)
open Langlands.Henniart.LocalNumerical (IsLadicContinuous IsLadicDefinedOverFiniteExtension)
open Langlands.LocalGalois.SepClosed (absoluteInertia)

namespace Langlands.Henniart.Laumon

/-- Laumon (2.1.2.4)–(2.1.2.6), in the form of the finite model of the positive breaks: for `ℓ`
different from the residue characteristic, every continuous ℓ-adic representation with a finite
model of the inertia group has a model with finite image, of the same rank, with the same
dimensions of fixed vectors under every upper ramification group `G^u`, `u > 0`. -/
def FiniteInertiaPositiveBreakModelStatement.{u₁, u₂, u₄} : Prop :=
  ∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ A : FiniteRepresentation.{0, u₂, u₄} (PadicAlgCl ℓ) (absoluteInertia K Ω),
      IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
      ∃ B : FiniteRepresentation.{0, u₂, u₄} (PadicAlgCl ℓ) (absoluteInertia K Ω),
        IsLadicContinuous ℓ B ∧ IsLadicDefinedOverFiniteExtension ℓ B ∧
        (Set.range B.representation).Finite ∧ B.rank = A.rank ∧
        ∀ u : ℝ, 0 < u →
          Module.finrank (PadicAlgCl ℓ) (fixedVectors B.representation
              ((localAbsoluteUpperRamificationGroup K Ω u).comap (absoluteInertia K Ω).subtype)) =
            Module.finrank (PadicAlgCl ℓ) (fixedVectors A.representation
              ((localAbsoluteUpperRamificationGroup K Ω u).comap (absoluteInertia K Ω).subtype))

/-- Laumon, Théorème (2.1.2.6): for `ℓ` different from the residue characteristic and a
continuous ℓ-adic representation with a finite model of a group `H` embedded in the Galois
group with image containing inertia, every slope is rational, `λ · dim W` is an integer for
every inertia-stable subspace `W` of the slope-`λ` summand (in particular for `W = V_λ`), and the
Swan conductor `s(V)` is a natural number. -/
def SlopeIntegralityStatement.{u₁, u₂, u₃, u₄} : Prop :=
  ∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (H : Type u₃) [Group H] [TopologicalSpace H] (f : H →* (Ω ≃ₐ[K] Ω)),
      Topology.IsEmbedding f → absoluteInertia K Ω ≤ f.range →
      ∀ A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H,
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
          (∀ μ ∈ slopeSupport f A, ∃ q : ℚ, (q : ℝ) = μ) ∧
          (∀ (μ : ℝ) (W : Submodule (PadicAlgCl ℓ) A), W ≤ slopeSummand f A μ →
            (∀ h : H, f h ∈ absoluteInertia K Ω → ∀ w ∈ W, A.representation h w ∈ W) →
            ∃ n : ℤ, μ * (Module.finrank (PadicAlgCl ℓ) W : ℝ) = n) ∧
          ∃ n : ℕ, ladicSwan f A = n

end Langlands.Henniart.Laumon
