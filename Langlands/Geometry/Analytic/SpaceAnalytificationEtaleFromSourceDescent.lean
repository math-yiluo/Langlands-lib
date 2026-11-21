import Langlands.Geometry.Analytic.AffineAnalytificationEtaleChartReflection
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleProof
import Langlands.Geometry.Analytic.ConditionalLocalizedEtalePullback
import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesProof
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityOfDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReflection

/-! # Reflection of étaleness under analytification of algebraic spaces -/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open AffinoidAtlasPresentation.StrongHom PresentedAffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem localizedEtalePullbacks : LocalizedEtalePullbackStatement.{u, u} K :=
  localizedEtalePullback_of_targetLocality_and_finitePieces
    (finiteOverTargetLocality_of_descent finiteAffinoidAlgebraDescent) finitePiecesEtaleAllPieces

private theorem affineRingHom_etale_of_localizedHom_etale
    (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (hf : etale (AffineAnalytification.localizedHom K P Q f)) :
    f.toRingHom.Etale :=
  ringHom_etale_of_localizedHom_etale K AffineAnalytification.affineAnalytificationEtale
    (fun _ _ _ _ _ _ P Q f hf => AffineAnalytification.isEtale_of_localizedHom_etale P Q f hf)
    P Q f hf

/-- Étaleness of a compatible map of analytifications implies étaleness of
the algebraic-space morphism. -/
theorem isEtaleMorphism_of_etale
    {X' X : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
    (hX'LFT : LocallyOfFiniteTypeOverBase X')
    (hXsep : IsSeparated X) (hXLFT : LocallyOfFiniteTypeOverBase X)
    {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
    {p' : PointFamily K X' Y'} {p : PointFamily K X Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (F : Y' ⟶ Y)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    (hEtale : etale F) : IsEtaleMorphism f := by
  apply (isEtaleMorphism_iff_finiteTypeAffineTests f hX'LFT).mpr
  intro A _ _ _ x hx
  let P := FinitePolynomialPresentation.ofFiniteType K A
  have hComp := etale_comp (hp'.etale_map P x hx) hEtale
  rw [hF] at hComp
  have hPoint := isEtale_pointHom_of_etale_of_affineReflection K (localizedEtalePullbacks K)
    (affineRingHom_etale_of_localizedHom_etale K) hXsep hXLFT hp P _ hComp
  simpa only [pointHom_map] using hPoint

/-- Étale descent along a jointly surjective étale source family is enough
to finish the algebraic-space comparison. -/
theorem spaceAnalytificationEtaleStatement_of_sourceDescent
    (hSource : ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
      (X Y : LocalizedCategory.{u, u, u} (K := K)) (F : X ⟶ Y)
      (ι : Type (u + 1)) (U : ι → LocalizedCategory.{u, u, u} (K := K))
      (q : ∀ i, U i ⟶ X),
      (∀ i, etale (q i)) →
      (∀ x : localizedSpaceFunctor.obj X,
        ∃ i, x ∈ Set.range (localizedSpaceFunctor.map (q i))) →
      (∀ i, etale (q i ≫ F)) → etale F) :
    SpaceAnalytificationEtaleStatement.{u} := by
  intro K _ _ _ X' X f _ hX'LFT hXsep hXLFT Y' Y p' p hp' hp F hF
  exact ⟨etale_of_isEtaleMorphism_of_sourceDescent K hSource f hp' hp F hF,
    isEtaleMorphism_of_etale K f hX'LFT hXsep hXLFT hp' hp F hF⟩

end Langlands.Analytic.SpaceAnalytification
