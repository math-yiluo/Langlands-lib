import Langlands.Geometry.Analytic.SpaceAnalytificationExistencePullback
import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceCharts
import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceAffinePullbacks
import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceStatement
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.LocalizedPullbackPoints

/-! # Conditional existence of analytifications of separated algebraic spaces

The glued point family of an analytic chart quotient is an analytification. Hence the
existence statement follows from an analytic quotient of every étale affine chart family
and the analytic inputs collected in `AnalyticInputs`; the covering family of étale affine
charts is constructed from an étale atlas. Inputs that are not yet Library statements are
written out as explicit hypotheses.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- The glued point family of an analytic chart quotient is an analytification. -/
theorem isAnalytification_pointFamily (H : AnalyticInputs K) (hX : IsSeparated X)
    {D : ChartData X} (E : QuotientData D) :
    IsAnalytification K X E.Y (pointFamily H hX E) where
  naturality P Q f x := pointFamily_naturality H hX E P Q f x
  etale_map P x hx := pointFamily_etale H hX E P x hx
  jointly_surjective := pointFamily_jointly_surjective H hX E
  isPullback P Q R f g x y h := pointFamily_isPullback H hX E P Q R f g x y h

/-- An analytification exists once a covering chart family has an analytic quotient and the
analytic inputs are available. -/
theorem exists_isAnalytification (H : AnalyticInputs K) (hX : IsSeparated X)
    {D : ChartData X} (E : QuotientData D) :
    ∃ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
      IsAnalytification K X Y p :=
  ⟨E.Y, pointFamily H hX E, isAnalytification_pointFamily H hX E⟩

/-- Conditional existence of analytifications: if every covering chart family of a separated
algebraic space has an analytic quotient and the analytic inputs hold over every field, then
`SpaceAnalytificationExistenceStatement` holds. The covering chart family is constructed from
an étale atlas (`nonempty_chartData`). -/
theorem spaceAnalytificationExistenceStatement_of_inputs
    (hQuot : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K] (X : AlgebraicSpace (Spec (CommRingCat.of K))), IsSeparated X →
      ∀ D : ChartData X, Nonempty (QuotientData D))
    (hInputs : ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K], AnalyticInputs K) :
    SpaceAnalytificationExistenceStatement.{u} := by
  intro K _ _ _ X hX hLFT
  obtain ⟨D⟩ := nonempty_chartData hLFT
  obtain ⟨E⟩ := hQuot K X hX D
  exact exists_isAnalytification (hInputs K) hX E

/-- The conditional existence statement: seven explicit inputs imply
`SpaceAnalytificationExistenceStatement.{u}`. In order, the hypotheses are

1. analytic quotients of étale affine chart families of separated algebraic spaces
   (Conrad–Temkin, Theorem 4.2.2, in the chart form proposed as
   `SpaceAnalytificationChartQuotientStatement`);
2. morphisms to an analytic space form a sheaf on the étale site (proposed as
   `EtaleHomSheafStatement.{u, u}`);
3. étaleness descends through jointly surjective étale families (proposed as
   `LocalizedEtaleSourceDescentStatement.{u, u, u}`);
4. the Library statement `AffineAnalytificationFibreProductStatement.{u, u, u, u}`;
5. analytifications of étale algebra maps are étale (proposed as
   `AffineAnalytificationLocalizedEtaleStatement.{u, u, u}`);
6. the Library statement `LocalizedEtalePullbackStatement.{u, u} K` over every field;
7. analytification preserves joint surjectivity from prime spectra to points (proposed as
   `AffineAnalytificationJointSurjectivityStatement.{u, u, u}`).

Inputs 1, 2, 3, 5 and 7 are not Library statements and are written out in full. -/
def SpaceAnalytificationExistenceReductionStatement : Prop :=
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
  AffineAnalytificationFibreProductStatement.{u, u, u, u} →
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (A : Type u) [CommRing A] [Algebra K A] (B : Type u) [CommRing B] [Algebra K B]
      (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
      (f : A →ₐ[K] B),
      f.toRingHom.Etale → etale (localizedHom K P Q f)) →
  (∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
      LocalizedEtalePullbackStatement.{u, u} K) →
  (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
      (ι : Type u) (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
      (Q : ∀ i, FinitePolynomialPresentation K (B i)) (f : ∀ i, A →ₐ[K] B i),
      (∀ 𝔭 : PrimeSpectrum A, ∃ i, ∃ 𝔮 : PrimeSpectrum (B i),
        PrimeSpectrum.comap (f i).toRingHom 𝔮 = 𝔭) →
      ∀ z : localizedSpaceFunctor.obj (localized K P),
        ∃ i, z ∈ Set.range (localizedSpaceFunctor.map (localizedHom K P (Q i) (f i)))) →
  SpaceAnalytificationExistenceStatement.{u}

/-- The conditional existence statement holds. The published localized functoriality of
affine analytification (`affineAnalytificationLocalizedFunctoriality`) and point lifting
through localized pullbacks (`exists_point_of_isPullback`) discharge the remaining fields of
`AnalyticInputs`. -/
theorem spaceAnalytificationExistenceReduction :
    SpaceAnalytificationExistenceReductionStatement.{u} := by
  intro hQ hSheaf hDesc hFib hEt hBase hSurj
  refine spaceAnalytificationExistenceStatement_of_inputs ?_ ?_
  · intro K _ _ _ X hX D
    obtain ⟨Y, π, hπ, hsurj, hpb⟩ :=
      hQ K X hX D.ι (fun i => D.A i) D.P D.x D.etale
    exact ⟨⟨Y, π, hπ, hsurj, fun i j _ _ _ Q f g h => hpb i j Q f g h⟩⟩
  · intro K _ _ _
    exact
      { sheaf := fun S T => hSheaf K S T
        descent := fun S T F J U q => hDesc K S T F J U q
        comp := fun P Q R f g =>
          (affineAnalytificationLocalizedFunctoriality.{u, u, u, u}
            K _ _ _ P P Q R f g).2.2.2.1
        id := fun P =>
          (affineAnalytificationLocalizedFunctoriality.{u, u, u, u} K _ _ _ P P P P
            (AlgHom.id K _) (AlgHom.id K _)).2.2.1
        affPullback := fun P Q R U f g a b h =>
          isPullback_localizedHom_of_isPullback_ty hFib
            affineAnalytificationLocalizedFunctoriality.{u, u, u, u} P Q R U f g a b h
        etaleFwd := fun P Q f hf => hEt K _ _ P Q f hf
        base := hBase K
        points := fun p q f g h _ a b hab => exists_point_of_isPullback p q f g h a b hab
        surj := fun P J B Q f hcov z => hSurj K _ P J (fun j => B j) Q f hcov z }

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
