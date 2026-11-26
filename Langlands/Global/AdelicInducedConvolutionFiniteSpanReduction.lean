import Langlands.Global.AdelicInducedConvolutionHolomorphy
import Langlands.Global.AdelicInducedConvolutionSmooth
import Langlands.Global.AdelicInducedConvolutionSquareIntegrability
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness

/-! # Finite span of the integrated induced action from a common center ideal and finiteness -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

/-- A single ideal of the ambient enveloping center, of finite complex codimension, annihilates
all plot-smooth infinite slices of the integrated induced action for a fixed input and kernel.
The parameter ranges over the whole complex character parameter space. -/
def InducedConvolutionUniformCenterIdealStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P),
    IsConnectedReductive G → IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsRationalLeviSubgroup l → IsIso (subgroupMultiplication l iU) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K),
      IsMaximalCompactSubgroup F G K → ∀ {d : ℕ}
      (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (φ v : AdelicGroupPoints F G → ℂ),
      Continuous φ → HasCompactSupport φ → IsAdelicSmoothFunction F G v →
      IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) v →
      IsCenterFiniteFunction F G hsmooth hcalc v →
      ∃ J : Ideal (AdelicEnvelopingCenter F G hsmooth),
        Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
        ∀ (lam : ComplexCharacterParameter F P) (z : AdelicEnvelopingCenter F G hsmooth), z ∈ J →
          ∀ (b : FiniteAdelicGroupPoints F G)
            (h : functionInfiniteSlice F G (hK.inducedConvolution lam φ v) b ∈
              InfinitePlotSmoothFunctions F G),
            plotSmoothCenterAction F G hsmooth hcalc z
              ⟨functionInfiniteSlice F G (hK.inducedConvolution lam φ v) b, h⟩ = 0

/-- The common annihilator and parabolic Harish-Chandra finiteness imply the finite-span
proposition with coefficients entire in the complex parameter. -/
def InducedConvolutionFiniteSpanReductionStatement : Prop :=
  InducedConvolutionUniformCenterIdealStatement → ParabolicHarishChandraFinitenessStatement.{0} →
    InducedConvolutionFiniteSpanStatement

set_option maxHeartbeats 800000 in
/-- Apply finiteness with the shared compact data, then extract a basis from the convolution
values using the pointwise entire evaluations. -/
theorem inducedConvolutionFiniteSpanReduction : InducedConvolutionFiniteSpanReductionStatement := by
  intro hcenter hHC F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ _ _ hG hU
    K hK N d rho hsmooth hcalc hmax hrho _ v hv φ hφ
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hp := r.isCompatible.parabolic
  have hl := r.isCompatible.levi
  have hiso := r.isIso_subgroupMultiplication_of_radical hU
  have hM := hl.isConnectedReductive
  have ha := hv.1
  have hs := ha.2.1
  obtain ⟨L, hL, E, hE, hcompact⟩ := inducedConvolutionCompactData F G P p K hK hmax φ v hφ hs.1
  have hleftU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) v :=
    fun g hg x => ha.1 g (Subgroup.mem_sup_left hg) x
  obtain ⟨J, hJ, hAnn⟩ := hcenter F G P M U p iU l hG hp hU hl hiso K hK hmax
    hsmooth hcalc φ v hφ.1 hφ.2.1 hs hleftU ha.2.2.2.1
  let f (lam : ComplexCharacterParameter F P) := hK.inducedConvolution lam φ v
  have hcov := inducedConvolutionParabolicCovariance F G P M U p iU l K hK v φ ha.1 hv.2.1
  have hsquare := inducedConvolutionWeightedSquare F G P M U p iU l K hK hM hU hiso φ v
    hφ.1 hφ.2.1 hs.1 ha.1 hv.2.1 hv.2.2
  have hauto (lam : ComplexCharacterParameter F P) :
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho (f lam) := by
    have hcont := hK.continuous_inducedConvolution lam hφ.1 hφ.2.1 hs.1
    have hplot := inducedConvolutionSmoothSlices F G P p K hK hsmooth hmax φ v hφ.1 hφ.2.1 hs lam
    have hbound := hK.hasModerateGrowthFunction_inducedConvolution lam rho hφ.1 hφ.2.1 ha.2.2.2.2
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
  let : Module.Finite ℤ (rationalCharacters P) := hp.finite_rationalCharacters hG
  obtain ⟨m, w, b, hw, hb, hsum⟩ := inducedConvolutionEntireCoefficients F G P p K hK φ v
    hφ.1 hφ.2.1 hs.1 hfamily
  refine ⟨m, w, b, fun i => ?_, hb, hsum⟩
  obtain ⟨lam, hi⟩ := hw i
  rw [← hi]
  exact hA2 lam

end Langlands.Global
