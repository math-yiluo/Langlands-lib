import Langlands.Global.AdelicInducedConvolutionFiniteSpanReduction
import Langlands.Global.AdelicNormalizedConvolutionHolomorphy

/-! # Finite square-integrable span of normalized convolutions on the imaginary axis

The common center ideal of the integrated induced action and parabolic Harish-Chandra
finiteness give a fixed finite family in `A²_P` whose span contains the normalized
convolutions at every imaginary parameter. No minimal parabolic in Iwasawa position for the
supplied compact is used. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

/-- The common annihilator of the integrated induced action and parabolic Harish-Chandra
finiteness imply the finite square-integrable span of the normalized convolutions on the
imaginary axis. -/
def NormalizedConvolutionImaginarySpanReductionStatement : Prop :=
  InducedConvolutionUniformCenterIdealStatement → ParabolicHarishChandraFinitenessStatement.{0} →
    NormalizedConvolutionImaginarySpanStatement

set_option maxHeartbeats 800000 in
/-- Apply finiteness to all convolution values with the shared level, compact coefficient space
and center ideal, then select a finite spanning subfamily of these values. -/
theorem normalizedConvolutionImaginarySpanReduction :
    NormalizedConvolutionImaginarySpanReductionStatement := by
  intro hcenter hHC F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ _ _ _ hG hU hiso _
    K hK N d rho hsmooth hcalc hmax hrho _ _ _ v hv kernel hk
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hp := r.isCompatible.parabolic
  have hl := r.isCompatible.levi
  have hM := hl.isConnectedReductive
  have ha := hv.1
  have hs := ha.2.1
  obtain ⟨L, hL, E, hE, hcompact⟩ := inducedConvolutionCompactData F G P p K hK hmax kernel v hk hs.1
  have hleftU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) v :=
    fun g hg x => ha.1 g (Subgroup.mem_sup_left hg) x
  obtain ⟨J, hJ, hAnn⟩ := hcenter F G P M U p iU l hG hp hU hl hiso K hK hmax
    hsmooth hcalc kernel v hk.1 hk.2.1 hs hleftU ha.2.2.2.1
  let f (lam : ComplexCharacterParameter F P) := hK.inducedConvolution lam kernel v
  have hcov := inducedConvolutionParabolicCovariance F G P M U p iU l K hK v kernel ha.1 hv.2.1
  have hsquare := inducedConvolutionWeightedSquare F G P M U p iU l K hK hM hU hiso kernel v
    hk.1 hk.2.1 hs.1 ha.1 hv.2.1 hv.2.2
  have hauto (lam : ComplexCharacterParameter F P) :
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho (f lam) := by
    have hcont := hK.continuous_inducedConvolution lam hk.1 hk.2.1 hs.1
    have hplot := inducedConvolutionSmoothSlices F G P p K hK hsmooth hmax kernel v hk.1 hk.2.1 hs lam
    have hbound := hK.hasModerateGrowthFunction_inducedConvolution lam rho hk.1 hk.2.1 ha.2.2.2.2
    exact ⟨(hcov lam).1, ⟨hcont, hplot, L, hL, (hcompact lam).1⟩,
      (hcompact lam).2.1, ⟨J, hJ, hAnn lam⟩, hbound⟩
  have hA2 (lam : ComplexCharacterParameter F P) :
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (f lam) :=
    ⟨hauto lam, (hcov lam).2, hsquare lam⟩
  have hfin := hHC F G P M U p iU l hG hp hU hl hiso K hmax hK rho hsmooth hcalc hrho
    J hJ L hL E hE
  have hfamily : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := by
    have sub (S : Set (AdelicGroupPoints F G → ℂ))
        (hS : FiniteDimensional ℂ (Submodule.span ℂ S)) (hle : Set.range f ⊆ S) :
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      Submodule.finiteDimensional_of_le (Submodule.span_mono hle)
    refine sub _ hfin ?_
    rintro _ ⟨lam, rfl⟩
    exact ⟨hauto lam, (hcompact lam).1, hAnn lam, (hcompact lam).2.2⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range f)).mp
    ((Submodule.fg_iff_finiteDimensional _).mpr hfamily)
  have hrange : Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) :
      AdelicGroupPoints F G → ℂ)) = (s : Set (AdelicGroupPoints F G → ℂ)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hw
      exact ⟨s.equivFin ⟨w, hw⟩, by simp⟩
  refine ⟨s.card, fun i => ((s.equivFin.symm i : s) : AdelicGroupPoints F G → ℂ),
    fun i => ?_, fun x => ?_⟩
  · obtain ⟨lam, hlam⟩ := hsS (s.equivFin.symm i).2
    dsimp only
    rw [← hlam]
    exact hA2 lam
  · rw [hrange, ← hspan]
    exact Submodule.subset_span ⟨imaginaryParameter F P x, rfl⟩

end Langlands.Global
