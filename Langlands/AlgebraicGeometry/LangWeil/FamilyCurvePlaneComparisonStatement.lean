import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilCurveStatement

/-!
# Uniform comparison of curve fibres with bounded-degree plane curves

This geometric prerequisite contains no square-root estimate. It isolates the
bounded plane-model comparison needed in the curve case of Lang–Weil.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Assuming the uniform upper bound, a family of geometrically irreducible
curves admits plane-curve comparisons over sufficiently large finite fields.
One integer bounds both bidegrees, the excluded field sizes and the discrepancy
between the actual fibre point count and the plane zero count. -/
def FamilyCurvePlaneComparisonStatement : Prop :=
  FamilyPointUpperBoundStatement.{u} →
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    LocallyOfFiniteType (specULiftZIsTerminal.{u}.from S) → CompactSpace S →
    LocallyOfFiniteType f → QuasiCompact f → GeometricallyIrreducible f →
    (∀ s : S, SchemeFiberGeometry.HasPureDimension (f.fiber s) 1) →
    ∃ B : ℕ, 0 < B ∧ ∀ (κ : Type u) [Field κ] [Finite κ]
      (s : Spec (CommRingCat.of κ) ⟶ S), B < Nat.card κ →
      ∃ p : MvPolynomial (Fin 2) κ,
        Irreducible (MvPolynomial.map (algebraMap κ (AlgebraicClosure κ)) p) ∧
        0 < p.degreeOf 0 ∧ p.degreeOf 0 ≤ B ∧
        0 < p.degreeOf 1 ∧ p.degreeOf 1 ≤ B ∧
        |(Nat.card {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = s} : ℝ) -
            (Nat.card {v : Fin 2 → κ // MvPolynomial.eval v p = 0} : ℝ)| ≤ (B : ℝ)

end Langlands.AlgebraicGeometry.LangWeil
