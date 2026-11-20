import Langlands.BaseChange.OrbitalIntegralPositivityStatement
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.Analysis.Local.QuotientMass
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Positivity of ordinary orbital integrals -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory QuotientIntegration TraceFormula
open scoped ComplexOrder

universe u

/-- A nonnegative Schwartz–Bruhat function that is positive at a regular semisimple element
has positive orbital integral for every compatible quotient measure. -/
theorem orbitalIntegralPositivity : OrbitalIntegralPositivityStatement.{u} := by
  intro F _ _ _ _ _ n μF _ f γ hγ hf hfγ μγ _ _ νγ hν
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient (glCentralizer γ)) := borel _
  let : BorelSpace (LeftQuotient (glCentralizer γ)) := ⟨rfl⟩
  let : T2Space F := LocalFieldTopology.t2Space F
  let : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : SigmaCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_sigmaCompactSpace F n
  let : νγ.Regular := hν.regular
  let : νγ.IsOpenPosMeasure := hν.isOpenPosMeasure
  let g := twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ (f : GeneralLinear n F → ℂ)
  have hg_cont : Continuous g := by
    dsimp only [g]
    rw [regularSemisimpleOrbitFunction_eq_comp γ hγ]
    exact f.continuous.comp
      (continuous_subtype_val.comp (regularSemisimpleOrbitHomeomorph γ hγ).continuous)
  have hg_comp : HasCompactSupport g :=
    hasCompactSupport_regularSemisimpleOrbitFunction γ hγ f.hasCompactSupport
  have hg_nonneg (q : LeftQuotient (glCentralizer γ)) : 0 ≤ g q := by
    induction q using Quotient.inductionOn with
    | h x =>
      dsimp only [g, twistedOrbitFunction_mk, MonoidHom.id_apply]
      exact hf _
  let r : LeftQuotient (glCentralizer γ) → ℝ := fun q => (g q).re
  have hr_cont : Continuous r := Complex.continuous_re.comp hg_cont
  have hr_comp : HasCompactSupport r := hg_comp.comp_left Complex.zero_re
  have hr_nonneg : 0 ≤ r := fun q => (Complex.nonneg_iff.mp (hg_nonneg q)).1
  have hr_pos : 0 < r (leftQuotientMap (glCentralizer γ) 1) := by
    change 0 < (f ((1 : GeneralLinear n F)⁻¹ * γ * 1)).re
    simpa only [inv_one, one_mul, mul_one] using (Complex.pos_iff.mp hfγ).1
  have hr_integral : 0 < ∫ q, r q ∂νγ :=
    hr_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hr_comp hr_nonneg hr_pos.ne'
  have hg_real : g = fun q => (r q : ℂ) := by
    funext q
    exact Complex.ext rfl (Complex.nonneg_iff.mp (hg_nonneg q)).2.symm
  change 0 < ∫ q, g q ∂νγ
  calc
    0 < ((∫ q, r q ∂νγ : ℝ) : ℂ) := Complex.zero_lt_real.mpr hr_integral
    _ = ∫ q, g q ∂νγ := by
      rw [hg_real]
      exact (integral_complex_ofReal (f := r) (μ := νγ)).symm

end Langlands.BaseChange
