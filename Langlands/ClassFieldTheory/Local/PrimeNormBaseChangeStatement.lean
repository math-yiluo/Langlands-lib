import Langlands.ClassFieldTheory.Local.ReciprocitySystem

/-! # Prime-degree norms after finite unramified base change -/

namespace Langlands.LocalClassField

universe u

/-- Every nonzero element of the base of a totally ramified prime-degree
Galois extension becomes a norm after an unramified Galois base extension
of degree at most that prime. The norm is the actual compositum norm. -/
def PrimeNormAfterUnramifiedBaseChange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field],
    let ell := Module.finrank F.Carrier E.field
    Nat.Prime ell →
      (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
          ell * F.canonicalTopologicalData.ramificationIndex →
        ∀ x : F.Carrierˣ,
          ∃ K' : FiniteIntermediateExtension F.Carrier,
            IsGalois F.Carrier K'.field ∧
            (K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
              F.canonicalTopologicalData.ramificationIndex ∧
            Module.finrank F.Carrier K'.field ≤ ell ∧
            ∃ M : FiniteIntermediateExtension F.Carrier,
              M.field = E.field ⊔ K'.field ∧
              ∃ h : K'.field ≤ M.field,
                ∃ y : M.fieldˣ,
                  FiniteIntermediateExtension.unitsNorm K' M h y =
                    Units.map (algebraMap F.Carrier K'.field).toMonoidHom x

end Langlands.LocalClassField
