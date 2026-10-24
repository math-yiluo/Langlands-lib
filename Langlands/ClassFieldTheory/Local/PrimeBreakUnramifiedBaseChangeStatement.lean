import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalFactor.Ramification.Galois

/-! Preservation of the actual prime ramification break under unramified base change. -/

namespace Langlands.LocalClassField

universe u

/-- The actual single lower break is unchanged by any finite unramified base
extension, using the canonical local data and the actual compositum inclusions. -/
def PrimeBreakUnramifiedBaseChange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E K' : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field],
    let ell := Module.finrank F.Carrier E.field
    Nat.Prime ell →
    (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        ell * F.canonicalTopologicalData.ramificationIndex →
    (K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        F.canonicalTopologicalData.ramificationIndex →
    ∀ (M : FiniteIntermediateExtension F.Carrier),
      M.field = E.field ⊔ K'.field →
      ∀ (hE : E.field ≤ M.field) (hK : K'.field ≤ M.field),
        letI := (E.asPadicField (p := p)).algebra
        letI := (K'.asPadicField (p := p)).algebra
        letI := (M.asPadicField (p := p)).algebra
        letI : Algebra E.field M.field := (IntermediateField.inclusion hE).toAlgebra
        letI : Algebra K'.field M.field := (IntermediateField.inclusion hK).toAlgebra
        letI : IsScalarTower (Padic p) F.Carrier E.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) E.field M.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) K'.field M.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        ∀ t : ℕ,
          (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup
            (E.asPadicField (p := p)).canonicalTopologicalData F.Carrier i =
              if i ≤ t then ⊤ else ⊥) →
          ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup
            (M.asPadicField (p := p)).canonicalTopologicalData K'.field i =
              if i ≤ t then ⊤ else ⊥

end Langlands.LocalClassField
