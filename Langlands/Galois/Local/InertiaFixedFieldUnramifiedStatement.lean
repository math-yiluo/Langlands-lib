import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.Normalization.Definitions

/-! # Finite unramified exhaustion of the actual inertia fixed field -/

namespace Langlands.PadicField

universe u

/-- The fixed field of the actual absolute inertia subgroup contains every
finite Galois intermediate extension with the same canonical absolute
ramification index as the base, and every finite subset of that fixed field
lies in one such extension. -/
def InertiaFixedFieldUnramifiedExhaustion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
    (∀ (E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier)
        [IsGalois F.Carrier E.field],
        F.canonicalTopologicalData.ramificationIndex =
            (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex →
          E.field ≤ U) ∧
      ∀ s : Finset (AlgebraicClosure F.Carrier), (∀ x ∈ s, x ∈ U) →
        ∃ E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier,
          ∃ _ : IsGalois F.Carrier E.field,
            F.canonicalTopologicalData.ramificationIndex =
                (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
              ∀ x ∈ s, x ∈ E.field

end Langlands.PadicField
