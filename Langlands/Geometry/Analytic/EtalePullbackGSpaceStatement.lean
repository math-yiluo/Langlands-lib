import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Langlands.Geometry.Analytic.EtaleSite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Statement: fibre products along étale morphisms of `G`-spaces are `G`-spaces -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Statement (implicit in Berkovich 1996, §1.2): let `p : P ⟶ A` and `q : P ⟶ B` form a
pullback of `f : A ⟶ Y` and `g : B ⟶ Y` in the localized category, with `f` étale and `A`, `B`,
`Y` Hausdorff. If a group `G` with a topology acts on `P`, `A` and `B`, the actions on `A` and `B`
are continuous, and `p`, `q` are equivariant, then `P` is Hausdorff and the action on `P` is
continuous. -/
def EtalePullbackGSpaceStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (G : Type z) [Group G] [TopologicalSpace G]
    {A B Y P : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : P ⟶ A) (q : P ⟶ B),
    etale f → IsPullback p q f g →
    T2Space (localizedSpaceFunctor.obj A) → T2Space (localizedSpaceFunctor.obj B) →
    T2Space (localizedSpaceFunctor.obj Y) →
    ∀ (σ : G →* Aut P) (σA : G →* Aut A) (σB : G →* Aut B),
      IsContinuousAction σA → IsContinuousAction σB →
      (∀ a, (σ a).asIso.hom ≫ p = p ≫ (σA a).asIso.hom) →
      (∀ a, (σ a).asIso.hom ≫ q = q ≫ (σB a).asIso.hom) →
      T2Space (localizedSpaceFunctor.obj P) ∧ IsContinuousAction σ

end Langlands.Analytic.SaturatedAtlasPresentation
