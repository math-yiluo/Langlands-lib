import Langlands.ClassFieldTheory.Local.FiniteComparison
import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.Normalization.Definitions

/-! # Exhaustion of absolute H2 by finite unramified extensions -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Every absolute degree-two class comes from a finite unramified Galois
intermediate extension, through the existing ordinary-to-continuous inflation. -/
def UnramifiedH2Exhaustion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (x : absoluteCohomology F.Carrier 2),
    ∃ E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier,
      ∃ _ : IsGalois F.Carrier E.field,
        F.canonicalTopologicalData.ramificationIndex =
            (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
          x ∈ (closureInflation F.Carrier E.field 2).range

end Langlands.ClassFieldTheory.Local
