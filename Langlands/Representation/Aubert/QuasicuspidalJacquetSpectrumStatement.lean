import Langlands.Representation.Aubert.QuasicuspidalJacquetClassStatement
import Langlands.Representation.Exponents.Jacquet

/-!
# Split-center spectrum of a supplied signed Aubert image

This conditional interface upgrades the quasicuspidal Jacquet class comparison
to generalized-character occurrence for actual admissible representations.
The reversed Jacquet action is transported literally to the target Levi.
-/

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Nonzero quasicuspidal reversed Jacquet data determine the sign and the
split-center generalized spectrum of an actual supplied signed Aubert image. -/
def QuasicuspidalJacquetSpectrumStatement : Prop := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact ∀ (n : ℕ) (B : BlockShape n)
    (π τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : π.HasFiniteLength) (hτ : τ.HasFiniteLength),
    IsAdmissible π.representation →
    IsAdmissible τ.representation →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    alternatingOperator.{uF, uV} F T n
        (GeneralLinear.finiteLengthClass n F.Carrier π hπ) =
      ε • GeneralLinear.finiteLengthClass n F.Carrier τ hτ →
    IsLeviQuasicuspidal B.reverse
      ((T.normalizedJacquetFunctor B.reverse).obj π).representation →
    Nontrivial ((T.normalizedJacquetFunctor B.reverse).obj π).obj →
    ε = (-1 : ℤ) ^ (n - B.length) ∧
      ∀ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
        IsGeneralizedEigencharacter (T.splitCentreJacquet B τ.representation) χ ↔
          IsGeneralizedEigencharacter
            ((transport B.reverse B B.reversePermutation
              (conjugatesLevi_reversePermutation F.Carrier B)
              (T.normalizedJacquet B.reverse π.representation)).comp
                (B.blockScalarLevi F.Carrier)) χ

end Langlands.Aubert
