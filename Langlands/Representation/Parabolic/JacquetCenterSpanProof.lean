import Langlands.Representation.Parabolic.JacquetCenterSpanStatement
import Langlands.Group.GL.BlockScalarCenter
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Parabolic.JacquetFiniteGenerationProof
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.Smooth.CentralOperatorExpansionProof

/-! Finite operator span of the actual unnormalized Jacquet block-scalar action. -/

noncomputable section

namespace Langlands.Parabolic

universe uF uV

section Transport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {m : ℕ} (B : GeneralLinear.BlockShape m)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Smooth finite type input has a finitely generated actual unnormalized
product-Levi radical quotient. -/
theorem finite_leviCoinvariants :
    letI := T.topology
    ∀ ρ : Representation ℂ (GeneralLinear m F.Carrier) V, IsSmooth ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear m F.Carrier)) ρ.asModule →
      Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
        (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)).asModule := by
  let := T.topology
  intro ρ hρ hfg
  have h := normalizedJacquetFiniteGeneration p F T m B V ρ hρ hfg
  rw [← twist_inverseHalfCharacter_leviCoinvariants F T B ρ] at h
  exact (finite_asModule_twist_iff _ _).mp h

end Transport

/-- The actual unnormalized Jacquet action of all block-scalar tuples has
finite-dimensional complex operator span for admissible finite-type input. -/
theorem jacquetCenterSpan : JacquetCenterSpanStatement.{uF, uV} := by
  intro p hp F T m B
  let := T.topology
  intro V hV hCV ρ hadm hfg σ
  exact centralActionSpan_finite σ (blockScalarCenter B)
    (isAdmissible_leviCoinvariants F T B V ρ hadm)
    (finite_leviCoinvariants T B ρ hadm.1 hfg)

end Langlands.Parabolic
