import Langlands.LocalField.Canonical
import Langlands.LocalField.Normalization.Definitions
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Trace.Basic

/-! Exact trace images of ideal powers at a prime ramification break. -/

namespace Langlands.LocalClassField

universe u v

/-- The exact image under the field trace of every nonnegative power of the
actual maximal ideal, for a prime totally ramified extension with the supplied
single lower ramification break. -/
def PrimeRamifiedTraceIdeals : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier],
    let ell := Module.finrank F.Carrier L.Carrier
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    Nat.Prime ell →
      TL.ramificationIndex = ell * TF.ramificationIndex →
        ∀ t : ℕ,
          (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup TL F.Carrier i =
            if i ≤ t then ⊤ else ⊥) →
          let d := (t + 1) * (ell - 1)
          ∀ n : ℕ,
            let r := (d + n) / ell
            ∀ y : F.Carrier,
              (∃ x : TL.Integers,
                x ∈ (IsLocalRing.maximalIdeal TL.Integers) ^ n ∧
                Algebra.trace F.Carrier L.Carrier (x : L.Carrier) = y) ↔
              (∃ a : TF.Integers,
                a ∈ (IsLocalRing.maximalIdeal TF.Integers) ^ r ∧
                (a : F.Carrier) = y)

end Langlands.LocalClassField
