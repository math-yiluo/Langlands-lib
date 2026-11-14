import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Statement: the fibral isomorphism criterion -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- **The fibral isomorphism criterion** (Conrad, *Reductive group schemes* (2014), Lemma B.3.1;
EGA IV₄ 17.9.5). Let `h : Y ⟶ Y'` be a morphism of schemes over a scheme `S`, where `Y` and `Y'`
are locally of finite presentation over `S` and `Y` is flat over `S`. If the base change
`h_s : Y_s ⟶ Y'_s` of `h` along `Spec κ(s) ⟶ S` is an isomorphism for every point `s` of `S`,
then `h` is an isomorphism. -/
def FibralIsomorphismStatement : Prop :=
  ∀ (S : Scheme.{u}) (Y Y' : Over S) (h : Y ⟶ Y'),
    LocallyOfFinitePresentation Y.hom → LocallyOfFinitePresentation Y'.hom → Flat Y.hom →
      (∀ s : S, IsIso ((Over.pullback (S.fromSpecResidueField s)).map h).left) →
        IsIso h.left

end Langlands.AlgebraicGeometry
