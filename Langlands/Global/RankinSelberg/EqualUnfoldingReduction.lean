import Langlands.Global.RankinSelberg.EqualUnfoldingCusp
import Langlands.Global.RankinSelberg.EqualUnfoldingIdele
import Langlands.Global.RankinSelberg.EqualUnfoldingStatement
import Langlands.Global.RankinSelberg.DualWhittakerExpansionStatement
import Langlands.Global.RankinSelberg.UnfoldingDual

/-! # A conditional reduction of the equal-rank unfolding statement

The Library statement `EqualUnfoldingStatement` (Cogdell 2004, §2.3, pp.210–211) follows from
four explicitly stated analytic premises for each pair of cuspidal realizations: the Whittaker
expansion of the cusp forms of the first realization, its dual analogue, and two gauge-type
integrability claims over `N_n(F) \ GL_n(𝔸)`. -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance equalReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

section Premises

/-- Gauge integrability, equal rank (Cogdell 2004, p.211): for `Re s` beyond a bound depending
only on the realizations, `g ↦ W_φ(g) φ'(g) Φ(e_n g) |det g|^s` is absolutely integrable over
`N_n(F) \ GL_n(𝔸)`, `n = r + 1`, uniformly over standard characters `ψ`, vectors and
Schwartz–Bruhat functions `Φ`. Here `W_φ` is the `ψ`-Whittaker function of `φ`. -/
def EqualWhittakerGaugeIntegrable {r : ℕ} (T T' : Automorphic.CuspidalOperatorRealization F r) :
    Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) → ∀ s : ℂ, C < s.re →
        Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
            cuspWhittaker F T ψ v q.out * cuspFunction F T' v' q.out *
              Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
          (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1)))

/-- Dual gauge integrability, equal rank (Cogdell 2004, p.211): the same claim for the dual
Whittaker function `W̃_φ = dualFunction W_φ`, the dual cusp form `φ̃'` and the Fourier transform
`Φ̂`: for `Re s` beyond a bound depending only on the realizations,
`g ↦ W̃_φ(g) φ̃'(g) Φ̂(e_n g) |det g|^s` is absolutely integrable over `N_n(F) \ GL_n(𝔸)`,
uniformly over standard `ψ`, vectors and Schwartz–Bruhat `Φ`. -/
def DualEqualWhittakerGaugeIntegrable {r : ℕ}
    (T T' : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) → ∀ s : ℂ, C < s.re →
        Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
            dualFunction F (r + 1) (cuspWhittaker F T ψ v) q.out *
              dualFunction F (r + 1) (cuspFunction F T' v') q.out *
              fourierTransform F (r + 1) ψ Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
          (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
            (isDiscrete_unipotentRationalImage F (r + 1)))

/-- The four retained premises for one equal-rank pair of cuspidal realizations. -/
def EqualUnfoldingPremises {r : ℕ} (T T' : Automorphic.CuspidalOperatorRealization F r) :
    Prop :=
  CuspidalWhittakerExpansion F T ∧ DualCuspidalWhittakerExpansion F T ∧
    EqualWhittakerGaugeIntegrable F T T' ∧ DualEqualWhittakerGaugeIntegrable F T T'

/-- The conditional reduction: the four premises for every equal-rank cuspidal pair imply
`EqualUnfoldingStatement`. -/
def EqualUnfoldingReductionStatement : Prop :=
  (∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r), EqualUnfoldingPremises F T T') →
  EqualUnfoldingStatement.{u}

end Premises

namespace EqualUnfolding

section Steps

variable {F} {r : ℕ}

omit [CompactSpace (AdeleQuotient F)] in
/-- The idele fiber mass `d^×a (D ∩ {c < |a| ≤ e c}) = 1` for the chosen fundamental domain
`D` of `F^×` in `𝔸^×`. -/
theorem ideleMeasure_ideleDomain_slab (c : ℝ) (hc : 0 < c) :
    ideleMeasure F (ideleDomain F ∩
      {z | c < detNorm F 1 z ∧ detNorm F 1 z ≤ Real.exp 1 * c}) = 1 :=
  ideleMeasure_fundamentalDomain_Ioc F (LeftCosetSpace.isFundamentalDomain _
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F 1)) Measure.haar) hc

/-- The gauge kernel of `(W_φ, φ')` gives integrability of the Whittaker integrand of
`(W_φ, W'_φ')`, where `W'_φ'` is the `ψ⁻¹`-Whittaker function of `φ'`. -/
theorem integrable_cuspWhittakerIntegrand (T T' : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (v' : T'.Space) {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1)) (s : ℂ)
    (hG : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        cuspWhittaker F T ψ v q.out * cuspFunction F T' v' q.out *
          Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1)))) :
    Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v')
      Φ s) (whittakerQuotientMeasure F (r + 1)) := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  exact integrable_equalWhittakerIntegrand_of_kernel F ψ hψ Φ s
    (measurable_cuspWhittaker F T ψ hψ v) (continuous_cuspFunction F T' v').measurable
    (measurable_cuspWhittaker F T' ψ⁻¹ hψ' v')
    (measurable_lastRow_comp (measurable_of_mem_schwartzBruhat F hΦ))
    (fun k hk x => cuspFunction_rational_mul F T' v' hk x)
    (cuspWhittaker_mul_left F T ψ hψ v)
    (fun n x => by rw [cuspWhittaker_mul_left F T' ψ⁻¹ hψ' v', genericCharacter_inv_eq_inv])
    (cuspWhittaker_inv_eq_setIntegral F T' ψ hψ v') hG

/-- The dual gauge kernel of `(W̃_φ, φ̃')` gives integrability of the Whittaker integrand of
`(W̃_φ, W̃'_φ')` with the Fourier transform `Φ̂`. -/
theorem integrable_dualCuspWhittakerIntegrand
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (v' : T'.Space) {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1)) (s : ℂ)
    (hG : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        dualFunction F (r + 1) (cuspWhittaker F T ψ v) q.out *
          dualFunction F (r + 1) (cuspFunction F T' v') q.out *
          fourierTransform F (r + 1) ψ Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1)))) :
    Integrable (equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ v))
      (dualFunction F (r + 1) (cuspWhittaker F T' ψ⁻¹ v')) (fourierTransform F (r + 1) ψ Φ) s)
      (whittakerQuotientMeasure F (r + 1)) := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  refine integrable_equalWhittakerIntegrand_of_kernel F ψ⁻¹ hψ' _ s
    ((measurable_cuspWhittaker F T ψ hψ v).comp (continuous_dualPoint F (r + 1)).measurable)
    (continuous_dualCuspFunction F T' v').measurable
    (measurable_dualCuspWhittaker F T' ψ hψ v')
    (measurable_lastRow_comp (EqualUnfolding.measurable_fourierTransform F ψ hψ hΦ))
    (fun k hk x => dualCuspFunction_rational_mul F T' v' hk x)
    (fun n x => ?_) (fun n x => ?_) (fun x => ?_) hG
  · have h := dualCuspWhittaker_unipotent_mul F T ψ⁻¹ hψ' v n x
    rwa [inv_inv] at h
  · rw [genericCharacter_inv_eq_inv, inv_inv]
    exact dualCuspWhittaker_unipotent_mul F T' ψ hψ v' n x
  · simp_rw [genericCharacter_inv_eq_inv]
    exact dualCuspWhittaker_eq_setIntegral F T' ψ hψ v' x

/-- The equal-rank unfolding at one point `s` (Cogdell 2004, §2.3, p.210): under the Whittaker
expansion of `φ` and the gauge integrability at `s`, the global integral `I(s; φ, φ', Φ)` and
the Whittaker integral `Ψ(s; W, W', Φ)` converge absolutely and agree. -/
theorem equal_unfolding_primal (T T' : Automorphic.CuspidalOperatorRealization F r)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (hω' : T'.realization.HasCentralCharacter ω') (hE : CuspidalWhittakerExpansion F T)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (v' : T'.Space) {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1)) (s : ℂ)
    (hG : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        cuspWhittaker F T ψ v q.out * cuspFunction F T' v' q.out *
          Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1)))) :
    Integrable (equalIntegrand F (ω * ω') (cuspFunction F T v) (cuspFunction F T' v') Φ s)
        (centralQuotientMeasure F (r + 1)) ∧
      Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ v)
        (cuspWhittaker F T' ψ⁻¹ v') Φ s) (whittakerQuotientMeasure F (r + 1)) ∧
      equalIntegral F (ω * ω') (cuspFunction F T v) (cuspFunction F T' v') Φ s =
        equalWhittakerIntegral F (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v') Φ s := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hΦm := measurable_of_mem_schwartzBruhat F hΦ
  obtain ⟨hint, hIeq, hWint⟩ := mirabolic_unfolding F ψ hψ Φ s
    (measurable_cuspWhittaker F T ψ hψ v) (continuous_cuspFunction F T' v').measurable
    (measurable_cuspWhittaker F T' ψ⁻¹ hψ' v') (measurable_lastRow_comp hΦm)
    (fun k hk x => cuspFunction_rational_mul F T' v' hk x)
    (cuspWhittaker_mul_left F T ψ hψ v)
    (fun n x => by rw [cuspWhittaker_mul_left F T' ψ⁻¹ hψ' v', genericCharacter_inv_eq_inv])
    (cuspWhittaker_inv_eq_setIntegral F T' ψ hψ v') (fun g => (hE ψ hψ v g).2) hG
  obtain ⟨hI, hKeq⟩ := eisenstein_unfolding ideleMeasure_ideleDomain_slab (ω * ω') s
    (continuous_cuspFunction F T v).measurable (continuous_cuspFunction F T' v').measurable hΦm
    (fun k hk x => cuspFunction_rational_mul F T v hk x)
    (fun k hk x => cuspFunction_rational_mul F T' v' hk x)
    (cuspFunction_mul_scalarPoint_mul F T T' hω hω' v v') hint
  exact ⟨hI, hWint, hKeq.trans hIeq⟩

/-- The dual equal-rank unfolding at one point `s` (Cogdell 2004, §2.3, p.211): under the
Whittaker expansion of `φ̃` and the dual gauge integrability at `s`, the integral
`I(s; φ̃, φ̃', Φ̂)` with character `(ω ω')⁻¹` and the Whittaker integral `Ψ(s; W̃, W̃', Φ̂)`
converge absolutely and agree. -/
theorem equal_unfolding_dual (T T' : Automorphic.CuspidalOperatorRealization F r)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (hω' : T'.realization.HasCentralCharacter ω') (hE : DualCuspidalWhittakerExpansion F T)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (v' : T'.Space) {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1)) (s : ℂ)
    (hG : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (r + 1)) =>
        dualFunction F (r + 1) (cuspWhittaker F T ψ v) q.out *
          dualFunction F (r + 1) (cuspFunction F T' v') q.out *
          fourierTransform F (r + 1) ψ Φ (lastRow F r q.out) * detPower F (r + 1) q.out s)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (r + 1))
        (isDiscrete_unipotentRationalImage F (r + 1)))) :
    Integrable (equalIntegrand F (ω * ω')⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
        (dualFunction F (r + 1) (cuspFunction F T' v')) (fourierTransform F (r + 1) ψ Φ) s)
        (centralQuotientMeasure F (r + 1)) ∧
      Integrable (equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ v))
        (dualFunction F (r + 1) (cuspWhittaker F T' ψ⁻¹ v')) (fourierTransform F (r + 1) ψ Φ) s)
        (whittakerQuotientMeasure F (r + 1)) ∧
      equalIntegral F (ω * ω')⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
          (dualFunction F (r + 1) (cuspFunction F T' v')) (fourierTransform F (r + 1) ψ Φ) s =
        equalWhittakerIntegral F (dualFunction F (r + 1) (cuspWhittaker F T ψ v))
          (dualFunction F (r + 1) (cuspWhittaker F T' ψ⁻¹ v')) (fourierTransform F (r + 1) ψ Φ)
          s := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hΦm := EqualUnfolding.measurable_fourierTransform F ψ hψ hΦ
  obtain ⟨hint, hIeq, hWint⟩ := mirabolic_unfolding F ψ⁻¹ hψ' (fourierTransform F (r + 1) ψ Φ) s
    ((measurable_cuspWhittaker F T ψ hψ v).comp (continuous_dualPoint F (r + 1)).measurable)
    (continuous_dualCuspFunction F T' v').measurable
    (measurable_dualCuspWhittaker F T' ψ hψ v') (measurable_lastRow_comp hΦm)
    (fun k hk x => dualCuspFunction_rational_mul F T' v' hk x)
    (fun n x => by
      have h := dualCuspWhittaker_unipotent_mul F T ψ⁻¹ hψ' v n x
      rwa [inv_inv] at h)
    (fun n x => by
      rw [genericCharacter_inv_eq_inv, inv_inv]
      exact dualCuspWhittaker_unipotent_mul F T' ψ hψ v' n x)
    (fun x => by
      simp_rw [genericCharacter_inv_eq_inv]
      exact dualCuspWhittaker_eq_setIntegral F T' ψ hψ v' x)
    (fun g => ((hE ψ hψ v).1 g).2) hG
  obtain ⟨hI, hKeq⟩ := eisenstein_unfolding ideleMeasure_ideleDomain_slab (ω * ω')⁻¹ s
    (continuous_dualCuspFunction F T v).measurable
    (continuous_dualCuspFunction F T' v').measurable hΦm
    (fun k hk x => dualCuspFunction_rational_mul F T v hk x)
    (fun k hk x => dualCuspFunction_rational_mul F T' v' hk x)
    (dualCuspFunction_mul_scalarPoint_mul F T T' hω hω' v v') hint
  exact ⟨hI, hWint, hKeq.trans hIeq⟩

end Steps

end EqualUnfolding

open EqualUnfolding

/-- The gauge premise alone gives the Whittaker-side integrability in `EqualUnfoldingStatement`:
for `Re s` beyond the gauge bound, `Ψ(s; W, W', Φ)` converges absolutely. -/
theorem integrable_equalWhittakerIntegrand_of_gauge {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    (hG : EqualWhittakerGaugeIntegrable F T T') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
        Φ ∈ schwartzBruhat F (r + 1) → ∀ s : ℂ, C < s.re →
          Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ v)
            (cuspWhittaker F T' ψ⁻¹ v') Φ s) (whittakerQuotientMeasure F (r + 1)) := by
  obtain ⟨C, hC, hG⟩ := hG
  exact ⟨C, hC, fun ψ hψ v v' Φ hΦ s hs =>
    integrable_cuspWhittakerIntegrand T T' ψ hψ v v' hΦ s (hG ψ hψ v v' Φ hΦ s hs)⟩

/-- The dual gauge premise alone gives the dual Whittaker-side integrability in
`EqualUnfoldingStatement`: for `Re s` beyond the dual gauge bound, `Ψ(s; W̃, W̃', Φ̂)`
converges absolutely. -/
theorem integrable_dualEqualWhittakerIntegrand_of_gauge {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    (hG : DualEqualWhittakerGaugeIntegrable F T T') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
        Φ ∈ schwartzBruhat F (r + 1) → ∀ s : ℂ, C < s.re →
          Integrable (equalWhittakerIntegrand F (dualFunction F (r + 1) (cuspWhittaker F T ψ v))
            (dualFunction F (r + 1) (cuspWhittaker F T' ψ⁻¹ v'))
            (fourierTransform F (r + 1) ψ Φ) s) (whittakerQuotientMeasure F (r + 1)) := by
  obtain ⟨C, hC, hG⟩ := hG
  exact ⟨C, hC, fun ψ hψ v v' Φ hΦ s hs =>
    integrable_dualCuspWhittakerIntegrand T T' ψ hψ v v' hΦ s (hG ψ hψ v v' Φ hΦ s hs)⟩

omit [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] in
/-- Proof of the conditional reduction. -/
theorem equalUnfoldingReduction : EqualUnfoldingReductionStatement.{u} := by
  intro hP F _ _ _ r T T' ω ω' hω hω'
  obtain ⟨hE, hEd, ⟨C₁, hC₁, hG⟩, ⟨C₂, hC₂, hGd⟩⟩ := hP F r T T'
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun ψ hψ v v' Φ hΦ => ?_⟩
  intro φ φ' W W' φdual φ'dual Wdual W'dual Φhat
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · exact equal_unfolding_primal T T' hω hω' hE ψ hψ v v' hΦ s
      (hG ψ hψ v v' Φ hΦ s (lt_of_le_of_lt (le_max_left _ _) hs))
  · have hs' : C₂ < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith [le_max_right C₁ C₂]
    exact equal_unfolding_dual T T' hω hω' hEd ψ hψ v v' hΦ (1 - s)
      (hGd ψ hψ v v' Φ hΦ (1 - s) hs')

end Langlands.Global.RankinSelbergGlobal
