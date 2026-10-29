import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Twist.LeviComplexPowerConjugationStatement

/-! # A pointwise cone bound for actual opposite Jacquet occurrences

This file states the cone bound as a proposition; it does not prove it.
-/

namespace Langlands

open GeneralLinear Geometric CuspidalSupport

universe uF uV uM

/-- An actual opposite Jacquet occurrence in an analytically tempered source
forces the transported negative real twist into the full diagonal positive
root cone. The source need not be irreducible. -/
def GLTemperedOppositeTwistConeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (C E : BlockShape n)
      (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) C E w)
      (ω : Rep.{uV} ℂ (C.Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ → IsAdmissible ω.ρ → IsUnitarizable ω.ρ →
      ∀ (v b : Fin C.length → ℝ)
        (A : Rep.{uM} ℂ (GeneralLinear n F.Carrier)),
        T.IsTempered A.ρ →
        T.IsOppositeJacquetClassExponent E A
          (Rep.of (transport C E w hw
            (T.leviComplexPowerTwist C
              (fun k => -(v k : ℂ) + Complex.I * (b k : ℂ)) ω.ρ))) →
          Exponents.IsClosedPositiveRootCone
            (fun a : Fin n => v (blockIndex C (w.symm a)))

end Langlands
