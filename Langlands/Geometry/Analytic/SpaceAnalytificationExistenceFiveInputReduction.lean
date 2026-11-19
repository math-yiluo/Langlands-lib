import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceReduction
import Langlands.Geometry.Analytic.AffineAnalytificationJointSurjectivity
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductProof

/-! # Conditional existence of analytifications from five inputs

Two of the seven inputs of `SpaceAnalytificationExistenceReductionStatement` are now proved:
input 4 by the published `affineAnalytificationFibreProduct`, and input 7 (joint surjectivity
of analytified spectrum-surjective families) by `exists_mem_range_localizedHom` in
`AffineAnalytificationJointSurjectivity`. This module removes both from the reduction. The
other five inputs are unchanged.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

/-- The conditional existence statement with five inputs: inputs 1, 2, 3, 5 and 6 of
`SpaceAnalytificationExistenceReductionStatement`, in the same order and form, imply
`SpaceAnalytificationExistenceStatement.{u}`. In order, the hypotheses are

1. analytic quotients of étale affine chart families of separated algebraic spaces
   (Conrad–Temkin, Theorem 4.2.2, in chart form);
2. morphisms to an analytic space form a sheaf on the étale site;
3. étaleness descends through jointly surjective étale families;
4. analytifications of étale algebra maps are étale (input 5 of the seven-input reduction);
5. the Library statement `LocalizedEtalePullbackStatement.{u, u} K` over every field
   (input 6 of the seven-input reduction).

Inputs 1–4 are not Library statements and are written out in full. -/
def SpaceAnalytificationExistenceFiveInputReductionStatement : Prop :=
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
      (A : Type u) [CommRing A] [Algebra K A] (B : Type u) [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B),
      f.toRingHom.Etale → etale (localizedHom K P Q f)) →
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtalePullbackStatement.{u, u} K) →
  SpaceAnalytificationExistenceStatement.{u}

/-- The five-input conditional existence statement holds: the published seven-input
reduction `spaceAnalytificationExistenceReduction` applies, with input 4 supplied by the
published `affineAnalytificationFibreProduct` and input 7 by
`exists_mem_range_localizedHom`. -/
theorem spaceAnalytificationExistenceFiveInputReduction :
    SpaceAnalytificationExistenceFiveInputReductionStatement.{u} := by
  intro hQ hSheaf hDesc hEt hBase
  exact spaceAnalytificationExistenceReduction hQ hSheaf hDesc
    affineAnalytificationFibreProduct.{u, u, u, u} hEt hBase
    fun K _ _ _ _ _ _ P _ _ _ _ Q f hcov z =>
      exists_mem_range_localizedHom K P Q f hcov z

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
