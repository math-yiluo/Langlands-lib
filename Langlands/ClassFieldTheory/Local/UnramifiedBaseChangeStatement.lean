import Langlands.ClassFieldTheory.Local.ReciprocitySystem

/-! # Finite unramified stages under a specified closure embedding -/

namespace Langlands.ClassFieldTheory.Local

universe u

open Langlands.LocalClassField

/-- A finite unramified Galois stage stays inside a finite unramified Galois
stage after any finite base extension, for the specified closure embedding. -/
def UnramifiedBaseChangeStageExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier)
      (AlgebraicClosure E.Carrier)]
    (L : FiniteIntermediateExtension F.Carrier)
    [IsGalois F.Carrier L.field],
    F.canonicalTopologicalData.ramificationIndex =
        (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex →
      ∃ M : FiniteIntermediateExtension E.Carrier,
        IsGalois E.Carrier M.field ∧
        E.canonicalTopologicalData.ramificationIndex =
          (M.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
        ∀ a : L.field,
          algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)
            (algebraMap L.field (AlgebraicClosure F.Carrier) a) ∈ M.field

end Langlands.ClassFieldTheory.Local
