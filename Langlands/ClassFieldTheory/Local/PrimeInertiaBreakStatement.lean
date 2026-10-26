import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Mathlib.FieldTheory.Galois.Basic

/-! A conditional single-break statement for the actual prime-degree filtration. -/

namespace Langlands.LocalClassField

universe u v

/-- Prime Galois degree and full actual inertia give one lower break and the
corresponding values of the actual inverse Herbrand function at natural inputs. -/
def PrimeInertiaBreakPattern : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
    (T : L.TopologicalData),
    let ell := Module.finrank F.Carrier L.Carrier
    Nat.Prime ell → Ramification.Padic.inertia T F.Carrier = ⊤ →
      ∃ t : ℕ,
        (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup T F.Carrier i =
          if i ≤ t then ⊤ else ⊥) ∧
        (0 < t ↔ Ramification.Padic.lowerRamificationGroup T F.Carrier 1 = ⊤) ∧
        ∀ n : ℕ, Ramification.Padic.herbrandPsi T F.Carrier (n : ℝ) =
          ((if n ≤ t then n else t + ell * (n - t) : ℕ) : ℝ)

end Langlands.LocalClassField
