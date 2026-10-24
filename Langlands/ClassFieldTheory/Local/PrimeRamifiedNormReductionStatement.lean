import Langlands.ClassFieldTheory.Local.Units
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.LocalField.Canonical
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Basic

/-! Exact higher-unit norms and critical representatives for a prime extension. -/

namespace Langlands.LocalClassField

universe u v

/-- In a prime totally ramified Galois extension, higher units are exact norms
at the inverse-Herbrand levels, and every norm class has a critical unit
representative. The break is specified by the actual lower groups. -/
def PrimeRamifiedNormReduction : Prop :=
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
          let ψ : ℕ → ℕ := fun n => if n ≤ t then n else t + ell * (n - t)
          let N := normUnits F.Carrier L.Carrier
          (∀ n : ℕ, t < n →
            (TL.unitFiltration (ψ n)).map N = TF.unitFiltration n) ∧
          (∀ n : ℕ, t ≤ n →
            (TL.unitFiltration (ψ n + 1)).map N = TF.unitFiltration (n + 1)) ∧
          (∀ x : F.Carrierˣ, ∃ y : L.Carrierˣ, ∃ z : TF.unitFiltration t,
            x = N y * (z : F.Carrierˣ))

end Langlands.LocalClassField
