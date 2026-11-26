import Langlands.Geometry.Analytic.EquivariantSitePullbacksStatement
import Langlands.Geometry.Analytic.QuasiEtaleSite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Statement: stability of quasi-étale morphisms under Hausdorff hypotheses
(Berkovich 1994, Lemma 3.1) -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Statement (Berkovich 1994, Lemma 3.1(i), compositions, for Hausdorff sources): if
`f : A ⟶ B` and `g : B ⟶ C` are quasi-étale and the underlying spaces of `A` and `B` are
Hausdorff, then `f ≫ g` is quasi-étale. -/
def QuasiEtaleHausdorffCompStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {A B C : LocalizedCategory.{u, v, v} (K := K)} (f : A ⟶ B) (g : B ⟶ C),
    T2Space (localizedSpaceFunctor.obj A) → T2Space (localizedSpaceFunctor.obj B) →
      quasiEtale f → quasiEtale g → quasiEtale (f ≫ g)

/-- Statement (Berkovich 1994, Lemma 3.1(i), base change, for Hausdorff sources): in every
pullback square `IsPullback f' g' g f` of localized analytic spaces, if `g : Y ⟶ S` is
quasi-étale and the underlying space of `Y` is Hausdorff, then the parallel projection
`g' : Y' ⟶ X` is quasi-étale. -/
def QuasiEtaleHausdorffBaseChangeStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {X Y Y' S : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → T2Space (localizedSpaceFunctor.obj Y) → quasiEtale g →
      quasiEtale g'

/-- Statement (Berkovich 1994, Lemma 3.1(ii), for a Hausdorff middle object): if
`g : Y ⟶ X` and `f ≫ g : Z ⟶ X` are quasi-étale and the underlying space of `Y` is
Hausdorff, then `f : Z ⟶ Y` is quasi-étale. No hypothesis is made on `Z` or `X`. -/
def QuasiEtaleHausdorffOverMorphismStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {X Y Z : LocalizedCategory.{u, v, v} (K := K)} (f : Z ⟶ Y) (g : Y ⟶ X),
    T2Space (localizedSpaceFunctor.obj Y) → quasiEtale g → quasiEtale (f ≫ g) →
      quasiEtale f

/-- Statement: the three Hausdorff stability statements above, for every complete
ultrametric normed field, imply that the equivariant quasi-étale sites `Qét(X(G))` have the
fibre products of `EquivariantQuasiEtalePullbacksStatement`. -/
def EquivariantQuasiEtalePullbacksHausdorffReductionStatement : Prop :=
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      QuasiEtaleHausdorffCompStatement.{u, v} K) →
    (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      QuasiEtaleHausdorffBaseChangeStatement.{u, v} K) →
    (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      QuasiEtaleHausdorffOverMorphismStatement.{u, v} K) →
    EquivariantQuasiEtalePullbacksStatement.{u, v, z}

end Langlands.Analytic.SaturatedAtlasPresentation
