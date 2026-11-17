import Langlands.Geometry.Analytic.SaturatedRecognitionCospans
import Langlands.Geometry.Analytic.FiniteChartFieldPointPullbacks
import Langlands.Geometry.Analytic.LocalizedFieldPointPullbackReduction

/-! # Full field-point pullbacks from finite recognized charts -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Limits Set PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] [IsAlgClosed L]
  {P A B X : SaturatedAtlasPresentation.{u, v, v} K}

/-- The literal pointed finite etale pair interface supplies the original
finite chart pairs used for full field-point lifting. -/
theorem HasPointedFiniteEtalePairs.hasFiniteChartPairs
    {f : A ⟶ X} {g : B ⟶ X} (h : HasPointedFiniteEtalePairs f g) :
    HasFiniteChartPairs f g := by
  intro a b hab
  obtain ⟨i, j, t, hf, hg, x, y, hx, hy, hfinite, _, _⟩ := h a b hab
  exact ⟨i, j, t, hf, hg, ⟨x, hx⟩, ⟨y, hy⟩, hfinite⟩

/-- The two algebraic comparison theorems suffice for full field-point
pullback preservation on every mapped strong etale cospan. -/
theorem strongEtaleFieldPointPullbackStatement_of_algebra
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) :
    StrongEtaleFieldPointPullbackStatement.{u, v, uL} K L := by
  intro P A B X r s f g hf hP
  let l := r ≫ recognitionSourceComparison f
  let m := s ≫ recognitionSourceComparison g
  have hR : IsPullback (localizationFunctor.map l) (localizationFunctor.map m)
      (localizationFunctor.map (recognitionMap f))
      (localizationFunctor.map (recognitionMap g)) := by
    apply hP.of_iso (Iso.refl _) (recognitionSourceIso f)
      (recognitionSourceIso g) (recognitionBaseIso X)
    · change localizationFunctor.map r ≫
          localizationFunctor.map (recognitionSourceComparison f) =
        𝟙 _ ≫ localizationFunctor.map l
      rw [Category.id_comp, ← Functor.map_comp]
    · change localizationFunctor.map s ≫
          localizationFunctor.map (recognitionSourceComparison g) =
        𝟙 _ ≫ localizationFunctor.map m
      rw [Category.id_comp, ← Functor.map_comp]
    · exact (recognitionMap_localized_square f).symm
    · exact (recognitionMap_localized_square g).symm
  have hfields := fieldPoint_isPullback_of_finiteChartPairs (L := L)
    hd hpush l m (recognitionMap f) (recognitionMap g) hR
    (recognitionMaps_hasPointedFiniteEtalePairs f g hf).hasFiniteChartPairs
  let E := localizedFieldPointFunctor (K := K) L
  apply hfields.of_iso' (E.mapIso (Iso.refl _)) (E.mapIso (recognitionSourceIso f))
    (E.mapIso (recognitionSourceIso g)) (E.mapIso (recognitionBaseIso X))
  · change E.map (𝟙 _) ≫ E.map (localizationFunctor.map l) =
      E.map (localizationFunctor.map r) ≫
        E.map (localizationFunctor.map (recognitionSourceComparison f))
    rw [E.map_id, Category.id_comp, ← E.map_comp, ← Functor.map_comp]
  · change E.map (𝟙 _) ≫ E.map (localizationFunctor.map m) =
      E.map (localizationFunctor.map s) ≫
        E.map (localizationFunctor.map (recognitionSourceComparison g))
    rw [E.map_id, Category.id_comp, ← E.map_comp, ← Functor.map_comp]
  · change E.map (recognitionSourceIso f).hom ≫
        E.map (localizationFunctor.map (recognitionMap f)) =
      E.map (localizationFunctor.map f) ≫ E.map (recognitionBaseIso X).hom
    rw [← E.map_comp, ← E.map_comp, recognitionMap_localized_square]
  · change E.map (recognitionSourceIso g).hom ≫
        E.map (localizationFunctor.map (recognitionMap g)) =
      E.map (localizationFunctor.map g) ≫ E.map (recognitionBaseIso X).hom
    rw [← E.map_comp, ← E.map_comp, recognitionMap_localized_square]

/-- The two algebraic comparison theorems suffice for the exact original
localized full field-point pullback-preservation proposition. -/
theorem localizedEtaleFieldPointPullbackStatement_of_algebra
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) :
    LocalizedEtaleFieldPointPullbackStatement.{u, v, uL} K L :=
  localizedEtaleFieldPointPullbackStatement_of_strong L
    (strongEtaleFieldPointPullbackStatement_of_algebra hd hpush)

/-- The original preservation proposition follows from the two independent
algebraic comparison propositions, with no extra geometric premise. -/
def AlgebraicEtaleFieldPointPullbackStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
    [IsUltrametricDist L] [IsAlgClosed L] : Prop :=
  DomainCompletedResidueSurjectivityStatement.{u} →
    AffinoidPushout.FiniteBanachPushoutStatement K →
      LocalizedEtaleFieldPointPullbackStatement.{u, v, uL} K L

/-- Full existence and uniqueness and recognition comparison prove the
algebraic-input reduction of the exact original proposition. -/
theorem algebraicEtaleFieldPointPullback :
    AlgebraicEtaleFieldPointPullbackStatement.{u, v, uL} K L :=
  fun hd hpush => localizedEtaleFieldPointPullbackStatement_of_algebra hd hpush

end Langlands.Analytic.SaturatedAtlasPresentation
