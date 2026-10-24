import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Mathlib.FieldTheory.Galois.Basic

/-! The actual single ramification break of a prime totally ramified extension. -/

namespace Langlands.LocalClassField

universe u v

/-- A prime-degree totally ramified Galois extension has one actual lower
ramification break, with the corresponding actual inverse-Herbrand formula. -/
def PrimeTotallyRamifiedBreak : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier],
    let ell := Module.finrank F.Carrier L.Carrier
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    Nat.Prime ell →
      TL.ramificationIndex = ell * TF.ramificationIndex →
        ∃ t : ℕ,
          (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup TL F.Carrier i =
            if i ≤ t then ⊤ else ⊥) ∧
          (0 < t ↔ ell = p) ∧
          ∀ n : ℕ, Ramification.Padic.herbrandPsi TL F.Carrier (n : ℝ) =
            ((if n ≤ t then n else t + ell * (n - t) : ℕ) : ℝ)

end Langlands.LocalClassField
