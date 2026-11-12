import Langlands.Representation.Classification.BernsteinUnitaryStatement

/-!
# Unitarizability of the shifted highest derivative

The unitarizability half of Tadic 1986, Theorem 2.5(iii) (Bernstein 1984, §7.4,
condition (ii)): for an irreducible unitarizable representation `π` of `GL_N`,
`N ≥ 1`, the shifted highest derivative `ν^(1/2) π^(h)` is unitarizable. It is
the second conjunct of `BernsteinShiftedHighestDerivativeUnitarity`, stated on
its own. This is a proposition definition; it is not proved here.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Bernstein 1984, §7.4(ii) (Tadic 1986, Theorem 2.5(iii), unitarizability
part): for an irreducible unitarizable representation `π` of `GL_N`, `N ≥ 1`,
the shifted highest derivative `ν^(1/2) π^(h)` is unitarizable. -/
def BernsteinShiftedHighestDerivativeUnitarizability : Prop :=
  letI := T.topology
  ∀ (N : ℕ), 0 < N →
    ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      Representation.IsIrreducible π.representation → IsUnitarizable π.representation →
        ∀ hd : Derivative.GeneralLinearHighestDerivativeOrderData T ψ π,
          IsUnitarizable (shiftedHighestDerivative F T ψ hd).representation

end Langlands.Classification
