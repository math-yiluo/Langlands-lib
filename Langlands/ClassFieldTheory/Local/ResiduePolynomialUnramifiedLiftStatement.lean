import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.RelativeIntegers
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Bounded unramified lifts of roots of residue polynomials -/

namespace Langlands.LocalClassField

universe u

/-- A nonconstant polynomial over the actual canonical residue field of `F`
acquires a root after a finite unramified Galois intermediate extension `K'`
of the specified algebraic closure, with `[K' : F]` at most its degree. The
polynomial is transported by the residue map induced by the actual inclusion
`F → K'`, with the packaged `Padic p`-algebra and composite scalar tower. -/
def ResiduePolynomialUnramifiedLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (P : Polynomial F.canonicalTopologicalData.ResidueField),
    0 < P.natDegree →
      ∃ K' : FiniteIntermediateExtension F.Carrier,
        IsGalois F.Carrier K'.field ∧
        (K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
          F.canonicalTopologicalData.ramificationIndex ∧
        Module.finrank F.Carrier K'.field ≤ P.natDegree ∧
        letI := (K'.asPadicField (p := p)).algebra
        letI : IsScalarTower (Padic p) F.Carrier
            (K'.asPadicField (p := p)).Carrier :=
          IsScalarTower.of_algebraMap_eq' rfl
        ∃ z : (K'.asPadicField (p := p)).canonicalTopologicalData.ResidueField,
          (P.map (PadicField.TopologicalData.relativeResidueMap
            (F := F) (E := K'.asPadicField (p := p))
            F.canonicalTopologicalData
            (K'.asPadicField (p := p)).canonicalTopologicalData)).eval z = 0

end Langlands.LocalClassField
