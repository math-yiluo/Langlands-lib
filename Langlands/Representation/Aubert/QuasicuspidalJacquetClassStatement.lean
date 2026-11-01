import Langlands.Representation.Aubert.JacquetCompatibilityStatement
import Langlands.Representation.CuspidalSupport.LeviDefinitions

/-!
# Actual Jacquet classes of a supplied signed Aubert image

This conditional proposition compares genuine Jacquet classes when the
reversed Jacquet module of the source is nonzero and quasicuspidal. It neither
constructs a signed Aubert image nor states an analytic classification.
-/

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A nonzero quasicuspidal reversed Jacquet module determines the sign of a
supplied actual signed Aubert image and identifies its actual Jacquet class
after the specified reversed-Levi transport. -/
def QuasicuspidalJacquetClassStatement : Prop := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact ∀ (n : ℕ) (B : BlockShape n)
    (π τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : π.HasFiniteLength) (hτ : τ.HasFiniteLength) (ε : ℤ),
    (ε = 1 ∨ ε = -1) →
    alternatingOperator.{uF, uV} F T n
        (GeneralLinear.finiteLengthClass n F.Carrier π hπ) =
      ε • GeneralLinear.finiteLengthClass n F.Carrier τ hτ →
    IsLeviQuasicuspidal B.reverse
      ((T.normalizedJacquetFunctor B.reverse).obj π).representation →
    Nontrivial ((T.normalizedJacquetFunctor B.reverse).obj π).obj →
    ε = (-1 : ℤ) ^ (n - B.length) ∧
      normalizedJacquetK0.{uF, uV} F T B
          (GeneralLinear.finiteLengthClass n F.Carrier τ hτ) =
        leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
          (conjugatesLevi_reversePermutation F.Carrier B)
          (normalizedJacquetK0.{uF, uV} F T B.reverse
            (GeneralLinear.finiteLengthClass n F.Carrier π hπ))

end Langlands.Aubert
