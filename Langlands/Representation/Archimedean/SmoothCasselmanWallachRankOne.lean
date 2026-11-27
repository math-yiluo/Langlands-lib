import Langlands.Representation.Archimedean.SmoothCasselmanWallachPrincipalSeries
import Langlands.Representation.Archimedean.SmoothCasselmanWallachFiniteDimensional
import Langlands.Representation.Archimedean.RealRankOneStandardModule

/-! # The Casselman–Wallach bound on the real general linear group of rank one -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open DerivativeSmoothVectors

universe uV uE₁ uE₂

local notation "G" => Langlands.GeneralLinear 1 ℝ
local notation "I" => matrixModel ℝ 1
local notation "M" => Matrix (Fin 1) (Fin 1) ℝ

/-- In rank one the Casselman–Wallach bound holds with only the empty word. -/
def RealSmoothCasselmanWallachRankOneStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin 1) ℝ) V)
    (π : (ℂ ⊗[ℝ] M) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E₁ : Type uE₁) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    (R₁ : G →* (E₁ →L[ℂ] E₁))
    (E₂ : Type uE₂) [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    (R₂ : G →* (E₂ →L[ℂ] E₂))
    (e : V ≃ₗ[ℂ] smoothKFinite ℝ 1 R₁)
    (f : V →ₗ[ℂ] DerivativeSmoothVectors I R₂),
    IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ → IsContinuousRepresentation R₁ →
    IsSmoothGKIntertwiner ℝ 1 R₁ ρ π ((smoothKFinite ℝ 1 R₁).subtype.comp e.toLinearMap) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v,
      ‖derivativeCLM I R₂ [] (f v)‖ ≤ C * ‖derivativeCLM I R₁ []
        (e v : DerivativeSmoothVectors I R₁)‖

/-- The rank-one principal series is one-dimensional, as is any of its nonzero irreducible
quotients. Apply the finite-dimensional word estimate to that quotient. -/
theorem realSmoothCasselmanWallachRankOne :
    RealSmoothCasselmanWallachRankOneStatement.{uV, uE₁, uE₂} := by
  intro V _ _ ρ π E₁ _ _ R₁ E₂ _ _ R₂ e f hirr hadm hR₁ he
  obtain ⟨cs, hcs, B, hB₀, hB⟩ := realPrincipalSeriesQuotient 1 V ρ π
    (isRealGKModule_of_smoothKFiniteEquiv hR₁ e he) hirr hadm
  obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hcs
  let B' : RealRankOneStandardModule.KF d →ₗ[ℂ] V := B
  let : FiniteDimensional ℂ (RealRankOneStandardModule.KF d) :=
    (RealRankOneStandardModule.evalEquiv d).symm.finiteDimensional
  let : FiniteDimensional ℂ V := Module.Finite.of_surjective B' (hB.surjective hirr hB₀)
  exact realSmoothCasselmanWallachFiniteDimensional 1 V E₁ R₁ E₂ R₂
    ((smoothKFinite ℝ 1 R₁).subtype.comp e.toLinearMap) f
    (Subtype.val_injective.comp e.injective)

end Langlands.Archimedean
