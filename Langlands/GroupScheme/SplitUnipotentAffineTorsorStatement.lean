import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Sections of split-unipotent torsors over affine schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual fpqc torsor under the pullback of a smooth affine split-unipotent
group over a field has a section over an arbitrary affine scheme over that field. -/
def SplitUnipotentAffineTorsorStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom],
    RelativeRoot.IsSplitUnipotent H →
    ∀ (T : Over (Spec (CommRingCat.of k))) [IsAffine T.left]
      (X : Over T.left)
      [ModObj ((GroupScheme.baseChange T.hom).obj H).X X],
      Flat X.hom → Surjective X.hom → QuasiCompact X.hom →
      IsIso (ModObj.leftSMul ((GroupScheme.baseChange T.hom).obj H).X X) →
      ∃ s : T.left ⟶ X.left, s ≫ X.hom = 𝟙 T.left

end Langlands.GroupScheme
