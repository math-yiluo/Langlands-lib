import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.AbelianScheme.Torsion

/-! # Raynaud's criterion for semiabelian reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Every `n`-torsion point of `B` with values in an algebraic closure of `K` is the
restriction of a `K`-point of `B`. -/
def HasRationalGeometricTorsion {K : Type u} [Field K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ) : Prop :=
  ∀ x ∈ GroupScheme.torsionPoints B.toGrp (n : ℤ)
      (Over.mk (Spec.algebraMap K (AlgebraicClosure K))),
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B.X,
      Over.homMk (Spec.algebraMap K (AlgebraicClosure K)) ≫ y = x

/-- An abelian variety over the fraction field of a discrete valuation ring whose
`n`-torsion points are all rational, for some `n ≥ 3` invertible in the valuation
ring, has semiabelian geometric special identity component in its Néron model. -/
def RaynaudSemiabelianCriterionStatement : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (B : AbelianScheme (Spec (CommRingCat.of K)))
    (N : NeronModel V K B) (n : ℕ), 3 ≤ n → IsUnit (n : V) →
      HasRationalGeometricTorsion B n → N.HasGeometricSemiabelianReduction

end Langlands.AbelianScheme
