import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceFiveInputReduction
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedEtaleReduction
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleProof

/-! # Conditional existence of analytifications: input 5 reduced to an index-universe comparison

Input 4 of `SpaceAnalytificationExistenceFiveInputReductionStatement` says that analytifications
of étale algebra maps are étale in the localized category. This module replaces it by a single
premise: the all-pieces to `strongEtale` direction of the published `strongEtale_ofSaturation_iff`
for original atlas index universe `0`. The published `affineAnalytificationEtale` and
`affineAnalytificationLocalizedEtaleReduction` supply the rest. The other four inputs are unchanged.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

/-- The conditional existence statement in which the étaleness input is reduced to an
index-universe comparison. In order, the hypotheses are

1. analytic quotients of étale affine chart families of separated algebraic spaces
   (Conrad–Temkin, Theorem 4.2.2, in chart form);
2. morphisms to an analytic space form a sheaf on the étale site;
3. étaleness descends through jointly surjective étale families;
4. for presentations with original atlas index universe `0`, a strong map between constructed
   saturations that is étale over all recognized pieces is `strongEtale` (the direction `←` of
   `strongEtale_ofSaturation_iff`, which the Library states only when the index universe equals
   the space universe);
5. `LocalizedEtalePullbackStatement.{u, u} K` over every complete ultrametric normed field `K`.

Hypotheses 1, 2, 3 and 5 are those of `SpaceAnalytificationExistenceFiveInputReductionStatement`,
in the same form. -/
def SpaceAnalytificationExistenceIndexUniverseReductionStatement : Prop :=
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X : AlgebraicSpace (Spec (CommRingCat.of K))), IsSeparated X →
      ∀ (ι : Type u) (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
        (P : ∀ i, FinitePolynomialPresentation K (A i)) (x : ∀ i, RingPoints K X (A i)),
        (∀ i, AlgebraicSpace.IsEtale (pointHom K (x i))) →
        ∃ (Y : LocalizedCategory.{u, u, u} (K := K))
          (π : ∀ i, AffineAnalytification.localized K (P i) ⟶ Y),
          (∀ i, SaturatedAtlasPresentation.etale (π i)) ∧
          (∀ y : localizedSpaceFunctor.obj Y,
            ∃ i, y ∈ Set.range (localizedSpaceFunctor.map (π i))) ∧
          ∀ (i j : ι) {B : Type u} [CommRing B] [Algebra K B]
            (Q : FinitePolynomialPresentation K B) (f : A i →ₐ[K] B) (g : A j →ₐ[K] B),
            IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
                ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
                (pointHom K (x i)) (pointHom K (x j)) →
              IsPullback (AffineAnalytification.localizedHom K (P i) Q f)
                (AffineAnalytification.localizedHom K (P j) Q g) (π i) (π j)) →
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X T : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology X)
        ((MorphismProperty.Over.forget _ _ X ⋙ Over.forget X).op ⋙ yoneda.obj T)) →
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : LocalizedCategory.{u, u, u} (K := K)) (F : X ⟶ Y)
      (ι : Type u) (U : ι → LocalizedCategory.{u, u, u} (K := K))
      (q : ∀ i, U i ⟶ X),
      (∀ i, etale (q i)) →
      (∀ x : localizedSpaceFunctor.obj X,
        ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
      (∀ i, etale (q i ≫ F)) → etale F) →
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : AffinoidAtlasPresentation.{u, u, 0} K) (g : ofSaturation X ⟶ ofSaturation Y),
      AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := X) (B := Y) g →
        strongEtale g) →
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtalePullbackStatement.{u, u} K) →
  SpaceAnalytificationExistenceStatement.{u}

/-- The conditional existence statement holds: the published five-input reduction applies, and
its étaleness input follows from `affineAnalytificationLocalizedEtaleReduction` applied to the
published `affineAnalytificationEtale` and the index-universe comparison. -/
theorem spaceAnalytificationExistenceIndexUniverseReduction :
    SpaceAnalytificationExistenceIndexUniverseReductionStatement.{u} := by
  intro hQ hSheaf hDesc hComp hBase
  exact spaceAnalytificationExistenceFiveInputReduction hQ hSheaf hDesc
    (affineAnalytificationLocalizedEtaleReduction affineAnalytificationEtale.{u, u, u} hComp)
    hBase

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
