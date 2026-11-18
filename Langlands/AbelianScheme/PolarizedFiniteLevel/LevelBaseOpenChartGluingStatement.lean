import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Representability of a Zariski sheaf on level bases from open charts -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Let `F` be a Zariski sheaf on the level base category of `n`. Suppose that the
functors of points of a family of level bases `X i` are identified with open
subfunctors of `F` by natural transformations `a i`, and that these open charts
cover `F`. Then `F` is represented by a level base `Y`. Moreover there are open
immersions `X i ⟶ Y` covering `Y` which induce the given charts. This
proposition is a statement, not a proof of it. -/
def LevelBaseOpenChartGluingStatement : Prop :=
  ∀ (n : ℕ) (F : (LevelBase n)ᵒᵖ ⥤ Type 1), LevelBase.IsZariskiSheaf F →
    ∀ (ι : Type) (X : ι → LevelBase n) (a : ∀ i, uliftYoneda.{1}.obj (X i) ⟶ F),
      (∀ i, LevelBase.IsOpenChart (a i)) → LevelBase.IsOpenChartCover a →
      ∃ (Y : LevelBase n) (e : uliftYoneda.{1}.obj Y ≅ F) (j : ∀ i, X i ⟶ Y),
        (∀ i, IsOpenImmersion (j i).hom) ∧
          (∀ y : Y.obj, ∃ i, y ∈ Set.range (j i).hom.base) ∧
          ∀ i, uliftYoneda.{1}.map (j i) ≫ e.hom = a i

end Langlands.AbelianScheme.PolarizedFiniteLevel
