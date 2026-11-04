import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite-morphism detection in actual affine scheme diagrams -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

/-- A finite morphism of actual affine scheme limits is detected after an
actual arrow to any finite-type stage with Cartesian transition squares. -/
def AffineDiagramFiniteDescent : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (E F : I ⥤ Scheme.{u})
    [∀ i, IsAffine (E.obj i)] [∀ i, IsAffine (F.obj i)]
    (α : E ⟶ F) (cE : Cone E) (cF : Cone F)
    (_hcE : IsLimit cE) (_hcF : IsLimit cF)
    (f : cE.pt ⟶ cF.pt)
    (_hf : ∀ i, cE.π.app i ≫ α.app i = f ≫ cF.π.app i)
    (i₀ : I) [LocallyOfFiniteType (α.app i₀)]
    (_hcart : ∀ {j : I} (r : j ⟶ i₀),
      IsPullback (E.map r) (α.app j) (α.app i₀) (F.map r)),
    IsFinite f →
      ∃ (j : I) (_r : j ⟶ i₀), IsFinite (α.app j)

end Langlands.AlgebraicGeometry.AffineLimit
