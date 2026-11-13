import Langlands.Representation.Parabolic.JacquetCenterSpanProof
import Langlands.AllField.Group.GL.BlockScalarCenter
import Langlands.AllField.Representation.Exponents.JacquetEigenvectorProof
import Langlands.AllField.Representation.Parabolic.JacquetCenterSpanStatement
import Langlands.AllField.Representation.Parabolic.JacquetFiniteGenerationProof
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-! Finite operator span of the actual unnormalized Jacquet block-scalar action. -/

noncomputable section

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding JacquetCenterSpanStatement NormalizedJacquetAdmissibilityClause NormalizedJacquetFiniteGenerationStatement ParabolicQuotientCompactClause UnipotentFiniteContainmentClause blockScalarCenter exists_iwahori_levi_subset finite_leviCoinvariants isAdmissible_leviCoinvariants isCompact_integralRange isSmooth_leviCoinvariants jacquetCenterSpan jacquetModuleEquiv_leviCoinvariants normalizedJacquetAdmissibility normalizedJacquetFiniteGeneration parabolicQuotientCompact quotientMap_image_integralRange twist_inverseHalfCharacter_leviCoinvariants twist_inverseHalfCharacter_leviCoinvariants_apply
open Langlands.AllField.Parabolic

universe uF uV

section Transport

variable {F : Type uF} [Field F] (T : LocalFieldData F)
variable {m : ℕ} (B : GeneralLinear.BlockShape m)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Smooth finite type input has a finitely generated actual unnormalized
product-Levi radical quotient. -/
theorem finite_leviCoinvariants :
    letI := T.topology
    ∀ ρ : Representation ℂ (GeneralLinear m F) V, IsSmooth ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear m F)) ρ.asModule →
      Module.Finite (MonoidAlgebra ℂ (B.Levi F))
        (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)).asModule := by
  let := T.topology
  intro ρ hρ hfg
  have h := normalizedJacquetFiniteGeneration F T m B V ρ hρ hfg
  rw [← twist_inverseHalfCharacter_leviCoinvariants F T B ρ] at h
  exact (finite_asModule_twist_iff _ _).mp h

end Transport

/-- The actual unnormalized Jacquet action of all block-scalar tuples has
finite-dimensional complex operator span for admissible finite-type input. -/
theorem jacquetCenterSpan : JacquetCenterSpanStatement.{uF, uV} := by
  intro F _ T m B
  let := T.topology
  intro V hV hCV ρ hadm hfg σ
  exact centralActionSpan_finite σ (blockScalarCenter B)
    (isAdmissible_leviCoinvariants F T B V ρ hadm)
    (finite_leviCoinvariants T B ρ hadm.1 hfg)

end Langlands.AllField.Parabolic
