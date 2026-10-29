import Langlands.ClassFieldTheory.Local.PrimeNormBaseChangeStatement
import Langlands.ClassFieldTheory.Local.Units
import Langlands.LocalFactor.Ramification.Galois

/-! Critical norm approximation after a bounded unramified base change. -/

namespace Langlands.LocalClassField

universe u

/-- The actual critical unit class becomes a graded norm after an unramified
Galois base extension of degree at most the prime degree. -/
def PrimeCriticalNormAfterUnramifiedBaseChange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field],
    letI := (E.asPadicField (p := p)).algebra
    letI : IsScalarTower (Padic p) F.Carrier E.field :=
      IsScalarTower.of_algebraMap_eq' rfl
    let ell := Module.finrank F.Carrier E.field
    let TF := F.canonicalTopologicalData
    let TE := (E.asPadicField (p := p)).canonicalTopologicalData
    Nat.Prime ell →
      TE.ramificationIndex = ell * TF.ramificationIndex →
        ∃ t : ℕ,
          (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup TE F.Carrier i =
            if i ≤ t then ⊤ else ⊥) ∧
          (0 < t ↔ ell = p) ∧
          ∀ z : TF.unitFiltration t,
            ∃ K : FiniteIntermediateExtension F.Carrier,
              IsGalois F.Carrier K.field ∧
              (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
                TF.ramificationIndex ∧
              Module.finrank F.Carrier K.field ≤ ell ∧
              ∃ M : FiniteIntermediateExtension F.Carrier,
                M.field = E.field ⊔ K.field ∧
                ∃ hE : E.field ≤ M.field, ∃ hK : K.field ≤ M.field,
                  letI := (K.asPadicField (p := p)).algebra
                  letI := (M.asPadicField (p := p)).algebra
                  letI : Algebra E.field M.field := (IntermediateField.inclusion hE).toAlgebra
                  letI : Algebra K.field M.field := (IntermediateField.inclusion hK).toAlgebra
                  letI : IsScalarTower F.Carrier E.field M.field :=
                    IsScalarTower.of_algebraMap_eq' rfl
                  letI : IsScalarTower F.Carrier K.field M.field :=
                    IsScalarTower.of_algebraMap_eq' rfl
                  letI : IsScalarTower (Padic p) F.Carrier K.field :=
                    IsScalarTower.of_algebraMap_eq' rfl
                  letI : IsScalarTower (Padic p) E.field M.field :=
                    IsScalarTower.of_algebraMap_eq' rfl
                  letI : IsScalarTower (Padic p) K.field M.field :=
                    IsScalarTower.of_algebraMap_eq' rfl
                  letI : FiniteDimensional K.field M.field :=
                    FiniteDimensional.right F.Carrier K.field M.field
                  let TK := (K.asPadicField (p := p)).canonicalTopologicalData
                  let TM := (M.asPadicField (p := p)).canonicalTopologicalData
                  Module.finrank K.field M.field = ell ∧
                  TM.ramificationIndex = ell * TK.ramificationIndex ∧
                  IsGalois K.field M.field ∧
                  (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup TM K.field i =
                    if i ≤ t then ⊤ else ⊥) ∧
                  ∃ y : TM.unitFiltration t,
                    Units.map (algebraMap F.Carrier K.field).toMonoidHom
                        (z : F.Carrierˣ) /
                      FiniteIntermediateExtension.unitsNorm K M hK (y : M.fieldˣ) ∈
                        TK.unitFiltration (t + 1)

end Langlands.LocalClassField
