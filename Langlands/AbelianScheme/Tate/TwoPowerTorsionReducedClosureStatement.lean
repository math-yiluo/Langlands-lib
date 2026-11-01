import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureSubgroupStatement
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Reduced scheme structure on the actual torsion closure -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

/-- The actual torsion closure admits its reduced closed scheme structure,
containing the unit and preserved by inversion and by its rational translations. -/
def TwoPowerTorsionReducedClosureStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    ∃ (Y : Scheme.{u}) (i : Y ⟶ A.X.left),
      IsClosedImmersion i ∧ IsReduced Y ∧
      Set.range i = closure (twoPowerTorsionLocus A) ∧
      (∃ e : Spec (CommRingCat.of K) ⟶ Y,
        e ≫ i = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left) ∧
      (∃ v : Y ≅ Y, v.hom ≫ i = i ≫ ι[A.X].left) ∧
      ∀ (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
        s.left (default : Spec (CommRingCat.of K)) ∈ closure (twoPowerTorsionLocus A) →
        ∃ t : Y ≅ Y, t.hom ≫ i = i ≫ (GrpObj.mulRight s).hom.left

end Langlands.AbelianScheme.Tate
