import Langlands.ClassFieldTheory.Local.Invariants
import Langlands.ClassFieldTheory.Local.ReciprocitySystem

/-! # Finite unramified extensions and arithmetic Frobenius coordinates -/

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- Every positive degree occurs for a finite unramified Galois intermediate
extension of the specified algebraic closure. -/
def UnramifiedExtensionDegreeExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (n : ℕ), 0 < n →
    ∃ E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier,
      ∃ _ : IsGalois F.Carrier E.field,
        F.canonicalTopologicalData.ramificationIndex =
            (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
          Module.finrank F.Carrier E.field = n

/-- Every compatible finite unramified Galois extension has a cyclic coordinate
whose positive generator acts by arithmetic Frobenius on the actual residue field. -/
def ArithmeticUnramifiedCoordinateExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsGalois F.Carrier E.Carrier],
    F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex →
    letI : NeZero (Module.finrank F.Carrier E.Carrier) := ⟨Module.finrank_pos.ne'⟩
    ∃ χ : Gal(E.Carrier/F.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier)),
      IsArithmeticUnramifiedCoordinate F E.Carrier χ

end Langlands.ClassFieldTheory.Local
