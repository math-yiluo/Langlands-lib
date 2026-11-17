import Langlands.Geometry.Analytic.RecognizedNestedPullback
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessStatement
import Langlands.Geometry.Analytic.AffinoidPointwiseReflection
import Langlands.Geometry.Analytic.PointwiseEtaleBoundedEquiv

/-! # Pointwise étaleness across nested recognized inverse-image squares -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- Conditional algebraic transport through the constructed recognized
square, with the substantial flatness and finite tensor comparison inputs
stated explicitly. -/
theorem recognizedNested_isEtaleAtPoint_iff
    (hflat : Domain.FlatnessStatement.{u})
    (hcomp : AffinoidPushout.FiniteTensorComparisonStatement K)
    (P₀ P : A.atlas.saturatedAtlas.RecognizedSubset)
    (W₀ W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h₀ : g.baseMap '' range P₀.chart ⊆ range W₀.chart)
    (h : g.baseMap '' range P.chart ⊆ range W.chart)
    (hW : W.locus ⊆ W₀.locus) (hP : P.locus ⊆ P₀.locus)
    (hpre : P.locus = P₀.locus ∩ g.baseMap ⁻¹' W.locus)
    (hf : (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsFiniteBanach)
    (t : BanachSpectrum P.algebra) :
    (g.fullRecognitionPairs.pullback P W h).IsEtaleAtPoint t ↔
      (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsEtaleAtPoint
        (BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t) := by
  let f := g.fullRecognitionPairs.pullback P₀ W₀ h₀
  let r := W.restriction W₀ hW
  let e := g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre
  let x := e.spectrumHomeomorph t
  have hc : Function.Bijective (AffinoidPushout.tensorComparison f r) :=
    hcomp W₀.algebra P₀.algebra W.algebra f r hf
  have hft : f.toAlgHom.toRingHom.FiniteType := hf.finite.finiteType
  have hrt := AffinoidPushout.rightMap_finiteType_of_tensorComparison f r hc hft
  have ht := BoundedAlgHom.isEtaleAtPoint_comp_boundedEquiv_iff
    (AffinoidPushout.rightMap f r) e hrt t
  rw [← g.fullRecognitionPairs_nestedPullback_eq_pushout P₀ P W₀ W h₀ hW hP hpre h] at ht
  have hp : BanachSpectrum.comap (AffinoidPushout.leftMap f r).toBoundedRingHom x =
      BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t := by
    change BanachSpectrum.comap
      (e.toBoundedAlgHom.comp (AffinoidPushout.leftMap f r)).toBoundedRingHom t = _
    rw [g.recognizedNestedPullbackEquiv_comp_leftMap P₀ P W₀ W h₀ hW hP hpre]
    rfl
  constructor
  · intro he
    have hx := ht.mp he
    have hF := AffinoidPushout.isEtaleAtPoint_of_rightMap_of_tensorComparison f r hc hft
      (hflat K W₀.algebra (W.inclusionDomain W₀ hW))
      (hflat K P₀.algebra (Domain.pullback f (W.inclusionDomain W₀ hW))) x hx
    rw [hp] at hF
    exact hF
  · intro he
    apply ht.mpr
    apply AffinoidPushout.rightMap_isEtaleAtPoint_of_tensorComparison f r hc hft x
    rw [hp]
    exact he

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
