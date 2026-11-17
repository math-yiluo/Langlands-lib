import Langlands.GroupScheme.SmoothDvrGenericAffinenessStatement
import Langlands.GroupScheme.DvrFiniteSmoothCoverStatement
import Langlands.GroupScheme.AffineQuotientReduction
import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent

/-! # Reduction of Raynaud affineness to the smooth case and a finite smooth cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The smooth DVR criterion and a finite smooth cover after a faithfully flat
DVR extension together imply the unchanged full DVR criterion. -/
def DvrGenericAffinenessReductionStatement : Prop :=
  SmoothDvrGenericAffinenessStatement.{u} →
    DvrFiniteSmoothCoverStatement.{u} → DvrGenericAffinenessStatement.{u}

namespace DvrGenericAffinenessReduction

/-- The smooth criterion and the finite smooth cover after DVR extension imply
Raynaud's full criterion, without changing its hypotheses or its universe. -/
theorem dvrGenericAffineness_of_smooth_and_cover
    (hSmooth : SmoothDvrGenericAffinenessStatement.{u})
    (hCover : DvrFiniteSmoothCoverStatement.{u}) : DvrGenericAffinenessStatement.{u} := by
  intro R _ _ _ K _ _ _ G hflat hft hqc hgen
  constructor
  · intro h
    have := h
    infer_instance
  · intro hsep
    obtain ⟨R', cR', dR', hDvr, b, hbflat, hbsurj, H, p, hSmoothH, hqcH, hsepH,
        hgenH, hfinite, hsurj⟩ := hCover R K G hflat hft hqc hsep hgen
    let := cR'
    have := dR'
    have := hDvr
    have hH : IsAffineHom H.X.hom :=
      hSmooth R' (FractionRing R') H hSmoothH hqcH hsepH hgenH
    have := hH
    have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    have := hfinite
    have := hsurj
    have hG' : IsAffine ((baseChange b).obj G).X.left :=
      AffineQuotient.isAffine_of_finite_surjective p.hom.hom hfinite hsurj
    have := hbflat
    have := hbsurj
    have : IsAffine (pullback G.X.hom b) := hG'
    have : IsAffine G.X.left :=
      Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent.isAffine_of_isPullback
        (IsPullback.of_hasPullback G.X.hom b)
    infer_instance

/-- The conditional reduction, with its two substantive inputs explicit. -/
theorem dvrGenericAffinenessReduction : DvrGenericAffinenessReductionStatement.{u} :=
  dvrGenericAffineness_of_smooth_and_cover

end DvrGenericAffinenessReduction

end Langlands.GroupScheme
