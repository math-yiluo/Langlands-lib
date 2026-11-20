import Langlands.Geometry.Analytic.ContinuousAnalyticAction

/-! # Near lifts along a strong map, at the level of strong maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Existence in Berkovich's Key Lemma 7.2 for commutative squares, stated for strong maps. For
every finite set `E` of test triples on the source of `g` there is a finite set `D` of test triples
on its target such that, whenever a strong map `y` into the target is `D`-near `x ≫ g` for a strong
map `x` into the source, after refining the common source along a quasi-isomorphism `r` there is
a strong map `x'` with `x' ≫ g = r ≫ y` that is `E`-near `r ≫ x`. -/
def HasStrongNearLifts {T B : SaturatedAtlasPresentation.{u, v, w} K} (g : T ⟶ B) : Prop :=
  ∀ E : Finset (TestTriple T), ∃ D : Finset (TestTriple B),
    ∀ (S : SaturatedAtlasPresentation.{u, v, w} K) (x : S ⟶ T) (y : S ⟶ B),
      (∀ τ ∈ D, StrongNear τ y (x ≫ g)) →
        ∃ (S' : SaturatedAtlasPresentation.{u, v, w} K) (r : S' ⟶ S) (_ : r.IsQuasiIso)
          (x' : S' ⟶ T), x' ≫ g = r ≫ y ∧ ∀ τ ∈ E, StrongNear τ x' (r ≫ x)

end Langlands.Analytic.SaturatedAtlasPresentation
