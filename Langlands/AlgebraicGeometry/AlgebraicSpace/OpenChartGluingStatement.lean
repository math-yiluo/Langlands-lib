import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Scheme representability from locally surjective open charts

This is the internal slice-fppf, lifted-value adaptation of Stacks Project
Lemma 26.15.4, Tag 01JJ. This module states the proposition without proving it.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An actual fppf sheaf covered locally by represented open charts is represented
by an actual scheme over the same base. -/
def OpenChartGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) (F : FppfSheaf S) (I : Type u)
    (U : I → Over S)
    (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ F.obj),
    (∀ k, IsOpenImmersion (a k)) →
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a) →
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ F.obj)

end Langlands.AlgebraicGeometry.AlgebraicSpace
