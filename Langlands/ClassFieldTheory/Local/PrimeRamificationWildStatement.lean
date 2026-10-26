import Langlands.LocalFactor.Ramification.Galois
import Langlands.LocalField.Canonical
import Mathlib.FieldTheory.Galois.Basic

/-! The prime-degree criterion for the actual first lower ramification group. -/

namespace Langlands.LocalClassField

universe u v

/-- In a prime-degree totally ramified Galois extension, the actual first lower
ramification group is the whole group exactly when the degree is the residue
characteristic. -/
def PrimeTotallyRamifiedWildCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier],
    let ell := Module.finrank F.Carrier L.Carrier
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    Nat.Prime ell →
      TL.ramificationIndex = ell * TF.ramificationIndex →
        (Ramification.Padic.lowerRamificationGroup TL F.Carrier 1 = ⊤ ↔ ell = p)

end Langlands.LocalClassField
