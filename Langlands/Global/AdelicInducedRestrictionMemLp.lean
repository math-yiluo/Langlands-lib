import Langlands.Global.AdelicInducedRestrictionMemLpStatement
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicInducedL2Inner

/-! # Square integrability of the restriction in Iwasawa coordinates

The restriction of an `A²_P` form descends continuously to `K × M(F) \ M(𝔸)`.
Its squared norm for the weighted measure is the integral of the extended norm of
`InducedInnerProductIntegrable.integrable_weightedSquare`'s integrand. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The restriction of an `A²_P` form represents an `L²` class for `inducedL2Measure`. -/
theorem inducedRestrictionMemLp : InducedRestrictionMemLpStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA _ π _ _ _ hlπ K hK N d rho
    hsmooth hcalc _ _ μM _ _ n e β hβc hβs hβ0 φ hφ
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hcont : Continuous (inducedRestriction K p l φ) := by
    unfold inducedRestriction
    apply LeftCosetSpace.continuous_out_of_invariant _
      (fun (k : K) m => φ (map F P G p (map F M P l m) * (k : AdelicGroupPoints F G)))
    · exact hφ.1.2.1.1.comp (((map F P G p).continuous.comp
        ((map F M P l).continuous.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst))
    · exact fun k _ hx m => InducedInnerProductIntegrable.form_rational_mul hφ.1.1 hx m k
  let μ₀ := (compactHaarProbability F G K hK.isCompact).prod
    (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM)
  let D : K × RationalQuotient F M → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (inducedWeight l e β x.2.out)
  have hD : Measurable D :=
    ENNReal.measurable_ofReal.comp ((measurable_inducedWeight_out l e β hβc).comp measurable_snd)
  have hweighted := InducedInnerProductIntegrable.integrable_weightedSquare e
    r.isCompatible.levi.isConnectedReductive r.isCompatible.splitComponent hA hlπ μM hβc hβs hφ
  change MemLp (inducedRestriction K p l φ) 2 (μ₀.withDensity D)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hsq : Continuous (fun z => ‖inducedRestriction K p l φ z‖ ^ 2) := hcont.norm.pow 2
  refine ⟨hsq.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_withDensity_eq_lintegral_mul μ₀ hD hsq.measurable.enorm]
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) hweighted.hasFiniteIntegral
  simp only [Pi.mul_apply, D, inducedWeight, inducedRestriction, enorm_mul, enorm_pow, enorm_norm]
  rw [ENNReal.ofReal_mul (hβ0 _), ofReal_norm, ← ofReal_norm ((β _) : ℂ),
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ0 _)]

end Langlands.Global
