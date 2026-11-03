import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSubsetSections
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenPullback

/-! # Full-domain comparison with actual ordinary-open pullback -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory RationalChart TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

/-- Actual quotient transport from an intrinsic rational chart gives an
ambient full-domain arrow with the original composite bounded map. -/
def rationalTransportInclusion (q : RationalChart K A)
    {w : RationalChart K d.algebra}
    (g : w ⟶ RationalChart.pullback d.baseMap q) :
    d.extend w.toDomain ⟶ q.toDomain where
  restriction := g.restriction.comp (pullbackMap d.baseMap q)
  comp_baseMap := by
    change g.restriction.comp ((pullbackMap d.baseMap q).comp q.baseMap) =
      w.baseMap.comp d.baseMap
    rw [pullbackMap_comp_baseMap, ← BoundedAlgHom.comp_assoc, g.comp_baseMap]

/-- Evaluation on an extended rational chart agrees with its actual bounded
quotient transport whenever it lies over a contained ambient chart. -/
theorem sectionEvaluation_extend_transport {S : Set (BanachSpectrum A)}
    (q : OpenSections.ChartIn S) (w : RationalChart K d.algebra)
    (hw : w.locus ⊆ d.spectrumMap ⁻¹' S)
    (g : w ⟶ RationalChart.pullback d.baseMap q.val)
    (s : OpenSections.Sections S) :
    sectionEvaluation (d.extend w.toDomain)
        (d.extend_locus_subset_of_preimage w.toDomain hw) s =
      g.restriction (pullbackMap d.baseMap q.val (s.val q)) := by
  have hn := (sectionEvaluation_naturality (d.rationalTransportInclusion q.val g)
    (d.extend_locus_subset_of_preimage w.toDomain hw) q.property s).symm
  rw [sectionEvaluation_rational] at hn
  exact hn

/-- On every ordinary ambient open, the full-domain evaluation construction
is precisely the previously constructed bounded-map pullback. -/
theorem toIntrinsicSections_eq_pullback (U : Opens (BanachSpectrum A)) :
    d.toIntrinsicSections (U : Set (BanachSpectrum A)) = OpenSections.pullback d.baseMap U := by
  apply AlgHom.ext
  intro s
  apply OpenSections.ext
  intro e
  let c := OpenSections.pullbackRefinement d.baseMap U e
  apply c.toFiniteCover.algebra_ext_of_restrict_eq
  intro i
  let hw : (c.chart i).locus ⊆ d.spectrumMap ⁻¹' (U : Set (BanachSpectrum A)) :=
    (c.map i).subset.trans e.property
  change (c.map i).restriction
      (sectionEvaluation (d.extend e.val.toDomain) _ s) =
    (c.map i).restriction (OpenSections.pullbackElement d.baseMap s e)
  exact (sectionEvaluation_naturality
    (d.extendFunctor.map ((toDomainFunctor K d.algebra).map (c.map i)))
    (d.extend_locus_subset_of_preimage (c.chart i).toDomain hw) _ s).trans
    ((d.sectionEvaluation_extend_transport (c.label i) (c.chart i) hw
      (OpenSections.pullbackRefinementMap d.baseMap U e i) s).trans
      (OpenSections.pullbackElement_local d.baseMap s e
        (c.label i) (c.chart i) (c.map i)
        (OpenSections.pullbackRefinementMap d.baseMap U e i)).symm)

/-- Actual ordinary-open pullback commutes with evaluation on every full
intrinsic domain, using its unchanged algebra after extension. -/
theorem sectionEvaluation_pullback (U : Opens (BanachSpectrum A))
    (V : Domain K d.algebra) (hV : V.locus ⊆ d.spectrumMap ⁻¹' (U : Set (BanachSpectrum A)))
    (s : OpenSections.Sections (U : Set (BanachSpectrum A))) :
    sectionEvaluation V hV (OpenSections.pullback d.baseMap U s) =
      sectionEvaluation (d.extend V)
        (d.extend_locus_subset_of_preimage V hV) s := by
  rw [← d.toIntrinsicSections_eq_pullback U]
  exact d.sectionEvaluation_toIntrinsicSections V hV s

/-- Returning the actual pulled-back section is the identity when the
ordinary open is contained in the domain's represented locus. -/
@[simp]
theorem fromIntrinsicSections_pullback (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) (s : OpenSections.Sections (U : Set (BanachSpectrum A))) :
    d.fromIntrinsicSections hU (OpenSections.pullback d.baseMap U s) = s := by
  rw [← d.toIntrinsicSections_eq_pullback U]
  exact d.fromIntrinsicSections_toIntrinsicSections hU s

/-- Actual pullback of a returned intrinsic section is the identity on the
full preimage of an ambient ordinary open contained in the domain. -/
@[simp]
theorem pullback_fromIntrinsicSections (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' (U : Set (BanachSpectrum A)))) :
    OpenSections.pullback d.baseMap U (d.fromIntrinsicSections hU s) = s := by
  rw [← d.toIntrinsicSections_eq_pullback U]
  exact d.toIntrinsicSections_fromIntrinsicSections hU s

/-- On any ambient ordinary open contained in a full domain, actual
bounded-map pullback is an algebra equivalence with the constructed inverse. -/
def openSectionsEquiv (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    OpenSections.Sections (U : Set (BanachSpectrum A)) ≃ₐ[K]
      OpenSections.Sections (d.spectrumMap ⁻¹' (U : Set (BanachSpectrum A))) :=
  d.subsetSectionsEquiv hU

/-- The forward map of the equivalence is the actual ordinary-open pullback. -/
theorem openSectionsEquiv_toAlgHom (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) :
    (d.openSectionsEquiv U hU).toAlgHom = OpenSections.pullback d.baseMap U :=
  d.toIntrinsicSections_eq_pullback U

@[simp]
theorem openSectionsEquiv_apply (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus) (s : OpenSections.Sections (U : Set (BanachSpectrum A))) :
    d.openSectionsEquiv U hU s = OpenSections.pullback d.baseMap U s :=
  congrArg (fun f => f s) (d.openSectionsEquiv_toAlgHom U hU)

@[simp]
theorem openSectionsEquiv_symm_apply (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus)
    (s : OpenSections.Sections (d.spectrumMap ⁻¹' (U : Set (BanachSpectrum A)))) :
    (d.openSectionsEquiv U hU).symm s = d.fromIntrinsicSections hU s := rfl

/-- The actual pullback equivalences commute with all restrictions between
ambient ordinary opens contained in the represented locus. -/
theorem openSectionsEquiv_restriction {U V : Opens (BanachSpectrum A)}
    (h : (U : Set (BanachSpectrum A)) ⊆ (V : Set (BanachSpectrum A))) (hV : (V : Set (BanachSpectrum A)) ⊆ d.locus)
    (s : OpenSections.Sections (V : Set (BanachSpectrum A))) :
    d.openSectionsEquiv U (h.trans hV) (OpenSections.restriction h s) =
      OpenSections.restriction (Set.preimage_mono h) (d.openSectionsEquiv V hV s) :=
  d.toIntrinsicSections_restriction h s

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
