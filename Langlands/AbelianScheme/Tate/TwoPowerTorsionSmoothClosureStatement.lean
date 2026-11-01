import Langlands.AbelianScheme.Tate.TwoPowerTorsionReducedClosureStatement

/-! # Smooth scheme structure on the actual torsion closure -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

/-- Over an algebraically closed field, the actual two-power torsion closure
admits a smooth closed scheme structure with the unit and the restrictions
of inversion and of all rational translations landing in the closure. -/
def TwoPowerTorsionSmoothClosureStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ (Y : Scheme.{u}) (i : Y ⟶ A.X.left),
      IsClosedImmersion i ∧ Smooth (i ≫ A.X.hom) ∧
      Set.range i = closure (twoPowerTorsionLocus A) ∧
      (∃ e : Spec (CommRingCat.of K) ⟶ Y,
        e ≫ i = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left) ∧
      (∃ v : Y ≅ Y, v.hom ≫ i = i ≫ ι[A.X].left) ∧
      ∀ (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
        s.left (default : Spec (CommRingCat.of K)) ∈ closure (twoPowerTorsionLocus A) →
        ∃ t : Y ≅ Y, t.hom ≫ i = i ≫ (GrpObj.mulRight s).hom.left

end Langlands.AbelianScheme.Tate
