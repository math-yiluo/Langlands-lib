import Langlands.Representation.GodementJacquet.WhittakerMatrixConvergence
import Langlands.Representation.GodementJacquet.WhittakerModelInclusion
import Langlands.Representation.RankinSelberg.ModelAsymptoticProof

/-!
# Whittaker integrals on the coefficient model

The functions of the coefficient model of a representation of Whittaker type
satisfy `IsWhittakerLike`, given the torus expansion of
`CoefficientTorusExpansion`. Hence their shifted full-matrix integrals converge
on a right half-plane and have rational continuations. This proves
`ModelWhittakerRationalityStatement` and `WhittakerModelComparisonStatement` from
`WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`. See the
paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear
open scoped BigOperators

universe uF uV

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelRationalityTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance modelRationalityValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance modelRationalityLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

variable {n : ℕ}

/-- The functions of the coefficient model of an admissible representation
with a torus expansion are Whittaker-like. -/
theorem glModelFunction_isWhittakerLike (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    IsWhittakerLike F ψ (glModelFunction ψ n σ ℓ w) where
  continuous := glModelFunction_continuous ψ n σ hσ.1 ℓ w
  equivariant := glModelFunction_equivariance ψ n σ ℓ w
  smooth := by
    obtain ⟨L, hL⟩ := (GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hσ).1 w
    refine ⟨L, fun g k hk => ?_⟩
    have hfix : glModelRepresentation ψ n σ ℓ k w = w := hL ⟨k, hk⟩
    rw [← glModelFunction_translate ψ n σ ℓ w k g, hfix]
  expansion := fun k => by
    obtain ⟨X, hX, hφ⟩ := hexp
    obtain ⟨φ, hφ'⟩ := hφ ℓ (glModelRepresentation ψ n σ ℓ k w)
    exact ⟨X, hX, φ, fun a => hφ' a⟩

/-- The shifted full-matrix integrals of a coefficient-model function converge on
a right half-plane and have a rational continuation in `q^(-s)`, given
`FiniteFunctionMellinStatement`, the torus expansion, and convergence of the
unshifted integrals on some right half-plane. -/
theorem glModel_shifted_of_converges (hFFM : FiniteFunctionMellinStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F.Carrier) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F.Carrier)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (hconv : ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      GodementJacquet.Padic.MatrixConverges F Φ s (glModelFunction ψ n σ ℓ w)) :
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n)
        (glModelFunction ψ n σ ℓ w)) ∧
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift n)
          (glModelFunction ψ n σ ℓ w)) R := by
  obtain ⟨c, hc⟩ := hconv
  refine ⟨⟨c - (jpssShift n).re, fun s hs => hc _ (by rw [Complex.add_re]; linarith)⟩, ?_⟩
  exact (glModelFunction_isWhittakerLike F ψ σ hσ hexp ℓ w).hasRationalContinuation F hFFM Φ
    (jpssShift n) ⟨c, hc⟩

/-- `ModelWhittakerRationalityStatement` follows from
`WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`. -/
theorem modelWhittakerRationality (hWTA : WhittakerTypeAsymptoticStatement.{uF, uV})
    (hFFM : FiniteFunctionMellinStatement.{uF}) :
    GodementJacquet.ModelWhittakerRationalityStatement.{uF, uV} := by
  intro p _ F ψ n V _ _ σ hσ ℓ _ Φ w
  have hexp := modelAsymptoticTransfer hWTA p inferInstance F F.canonicalTopologicalData n V σ ψ
    (standardCharacter ψ n) (Or.inl rfl) hσ
  exact glModel_shifted_of_converges F hFFM ψ σ hσ.1 hexp ℓ Φ w
    ((glModelFunction_isWhittakerLike F ψ σ hσ.1 hexp ℓ w).matrixConverges F hFFM Φ)

/-- `WhittakerModelComparisonStatement` follows from
`WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`. -/
theorem whittakerModelComparison_of_asymptotics
    (hWTA : WhittakerTypeAsymptoticStatement.{uF, uV})
    (hFFM : FiniteFunctionMellinStatement.{uF}) :
    GodementJacquet.WhittakerModelComparisonStatement.{uF, uV} :=
  GodementJacquet.whittakerModelComparison_of_rationality (modelWhittakerRationality hWTA hFFM)

end Padic

end Langlands.GodementJacquet.WhittakerTorus
