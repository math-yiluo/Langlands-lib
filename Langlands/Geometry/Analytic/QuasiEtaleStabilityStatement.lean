import Langlands.Geometry.Analytic.QuasiEtaleSite
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Statement: stability of quasi-étale morphisms (Berkovich 1994, Lemma 3.1) -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Statement (Berkovich 1994, Lemma 3.1(i), compositions): quasi-étale
morphisms of localized analytic spaces are stable under composition. -/
def QuasiEtaleCompStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  MorphismProperty.IsStableUnderComposition
    (quasiEtale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))

/-- Statement (Berkovich 1994, Lemma 3.1(i), base change): in every pullback
square of localized analytic spaces, the projection parallel to a quasi-étale
arrow is quasi-étale. -/
def QuasiEtaleBaseChangeStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  MorphismProperty.IsStableUnderBaseChange
    (quasiEtale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))

/-- Statement (Berkovich 1994, Lemma 3.1(ii)): if `g : Y ⟶ X` and
`f ≫ g : Z ⟶ X` are quasi-étale, then the `X`-morphism `f : Z ⟶ Y` is
quasi-étale. -/
def QuasiEtaleOverMorphismStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  MorphismProperty.HasOfPostcompProperty
    (quasiEtale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))
    (quasiEtale (K := K))

/-- Statement (Berkovich 1994, Lemma 3.1, without the ground field extension
clause): the conjunction of the three stability properties above. -/
def QuasiEtaleStabilityStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  QuasiEtaleCompStatement.{u, v} K ∧ QuasiEtaleBaseChangeStatement.{u, v} K ∧
    QuasiEtaleOverMorphismStatement.{u, v} K

end Langlands.Analytic.SaturatedAtlasPresentation
