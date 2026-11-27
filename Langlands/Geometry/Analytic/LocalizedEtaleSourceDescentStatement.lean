import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Source descent for localized étale morphisms -/

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Étaleness descends through a jointly surjective family of étale maps to the
source, in the Library's localized category of analytic spaces. The field, space and
index universes are independent. -/
def LocalizedEtaleSourceDescentStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X Y : LocalizedCategory.{u, v, v} (K := K)) (F : X ⟶ Y)
    (ι : Type w) (U : ι → LocalizedCategory.{u, v, v} (K := K))
    (q : ∀ i, U i ⟶ X),
    (∀ i, etale (q i)) →
    (∀ x : localizedSpaceFunctor.obj X,
      ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
    (∀ i, etale (q i ≫ F)) → etale F

end Langlands.Analytic.SaturatedAtlasPresentation
