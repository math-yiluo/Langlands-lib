import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.UrysohnsLemma

/-! # The quotient measure on `N \ GL_n(ℝ)` in logarithmic toral coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealIwasawa

open Langlands.Archimedean (unitaryCompact)
open Langlands.QuotientIntegration (LeftQuotient quotientAverage)

variable {n : ℕ}

/-! ### Topology of the unipotent group -/

theorem isClosed_upperUnipotent :
    IsClosed ((Langlands.GeneralLinear.upperUnipotent n ℝ : Subgroup (Langlands.GeneralLinear n ℝ)) :
      Set (Langlands.GeneralLinear n ℝ)) := by
  have hv : Continuous fun g : Langlands.GeneralLinear n ℝ => (g : Matrix (Fin n) (Fin n) ℝ) :=
    Units.continuous_val
  have h : ((Langlands.GeneralLinear.upperUnipotent n ℝ : Subgroup (Langlands.GeneralLinear n ℝ)) :
      Set (Langlands.GeneralLinear n ℝ)) =
      {g : Langlands.GeneralLinear n ℝ | (g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular} ∩
        ⋂ i : Fin n, {g : Langlands.GeneralLinear n ℝ | (g : Matrix (Fin n) (Fin n) ℝ) i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact (isClosed_setOfPred_blockTriangular.preimage hv).inter
    (isClosed_iInter fun i => isClosed_eq ((continuous_apply_apply i i).comp hv) continuous_const)

instance instLocallyCompactSpaceRealMatrix : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))

instance instLocallyCompactSpaceRealGL : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ)ˣ)

instance instLocallyCompactSpaceUpperUnipotent : LocallyCompactSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
  isClosed_upperUnipotent.locallyCompactSpace

/-- A nonnegative compactly supported continuous bump function on `N` with value one at the
identity. -/
theorem exists_unipotent_bump :
    ∃ β : Langlands.GeneralLinear.upperUnipotent n ℝ → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ u, 0 ≤ β u) ∧
      β 1 = 1 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : Langlands.GeneralLinear.upperUnipotent n ℝ))) isClosed_empty
    (Set.disjoint_empty _)
  exact ⟨f, f.continuous, hfc, fun u => (hf01 u).1, by simpa using hf1 (Set.mem_singleton _)⟩

/-! ### Conjugation by the torus as a homeomorphism of `N` -/

theorem conjTorus_neg_conjTorus (z : Fin n → ℝ) (u : Langlands.GeneralLinear.upperUnipotent n ℝ) :
    conjTorus (-z) (conjTorus z u) = u := by
  apply Subtype.ext
  change torus (-z) * (torus z * (u : Langlands.GeneralLinear n ℝ) * torus (-z)) *
    torus (-(-z)) = u
  rw [neg_neg, torus_neg]
  group

theorem conjTorus_zero (u : Langlands.GeneralLinear.upperUnipotent n ℝ) : conjTorus 0 u = u := by
  apply Subtype.ext
  change torus (0 : Fin n → ℝ) * (u : Langlands.GeneralLinear n ℝ) * torus (-(0 : Fin n → ℝ)) = u
  rw [neg_zero, torus_zero, one_mul, mul_one]

theorem continuous_conjTorus_right (z : Fin n → ℝ) : Continuous (conjTorus (n := n) z) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

/-- Conjugation by `torus z` as a homeomorphism of `N`. -/
def conjTorusHomeomorph (z : Fin n → ℝ) : Langlands.GeneralLinear.upperUnipotent n ℝ ≃ₜ Langlands.GeneralLinear.upperUnipotent n ℝ where
  toFun := conjTorus z
  invFun := conjTorus (-z)
  left_inv u := conjTorus_neg_conjTorus z u
  right_inv u := by simpa using conjTorus_neg_conjTorus (-z) u
  continuous_toFun := continuous_conjTorus_right z
  continuous_invFun := continuous_conjTorus_right (-z)

/-! ### Lifts of functions of the toral coordinate -/

theorem continuous_lift {φ : (Fin n → ℝ) → ℝ} {β : Langlands.GeneralLinear.upperUnipotent n ℝ → ℝ}
    (hφ : Continuous φ) (hβ : Continuous β) :
    Continuous fun g : Langlands.GeneralLinear n ℝ => φ (alpha g) * β (npart g) :=
  (hφ.comp continuous_alpha).mul (hβ.comp continuous_npart)

theorem hasCompactSupport_lift {φ : (Fin n → ℝ) → ℝ} {β : Langlands.GeneralLinear.upperUnipotent n ℝ → ℝ}
    (hφ : HasCompactSupport φ) (hβ : HasCompactSupport β) :
    HasCompactSupport fun g : Langlands.GeneralLinear n ℝ => φ (alpha g) * β (npart g) := by
  let P : Langlands.GeneralLinear.upperUnipotent n ℝ × (Fin n → ℝ) × unitaryCompact ℝ n → Langlands.GeneralLinear n ℝ :=
    fun p => (p.1 : Langlands.GeneralLinear n ℝ) * torus p.2.1 * (p.2.2 : Langlands.GeneralLinear n ℝ)
  have hP : Continuous P :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_torus.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  refine HasCompactSupport.intro ((hβ.isCompact.prod (hφ.isCompact.prod isCompact_univ)).image hP) ?_
  intro g hg
  by_contra hne
  apply hg
  have h1 : φ (alpha g) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : β (npart g) ≠ 0 := right_ne_zero_of_mul hne
  exact ⟨(npart g, alpha g, kpart g),
    ⟨subset_tsupport _ h2, subset_tsupport _ h1, Set.mem_univ _⟩, npart_mul_torus_mul_kpart g⟩


/-! ### The toral pushforward of the quotient measure -/

section Toral

variable [MeasurableSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]
  [BorelSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]

theorem measurable_alphaQ : Measurable (alphaQ (n := n)) :=
  continuous_alphaQ.measurable

theorem isFiniteMeasureOnCompacts_map_alphaQ
    (ν : Measure (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ)))
    [IsFiniteMeasureOnCompacts ν] : IsFiniteMeasureOnCompacts (ν.map alphaQ) :=
  ⟨fun K hK => by
    rw [map_apply measurable_alphaQ hK.measurableSet]
    exact (isCompact_alphaQ_preimage hK).measure_lt_top⟩

theorem integral_map_alphaQ
    (ν : Measure (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ)))
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂(ν.map alphaQ) = ∫ q, φ (alphaQ q) ∂ν :=
  integral_map measurable_alphaQ.aemeasurable hφ.aestronglyMeasurable

end Toral

theorem conjTorus_one (z : Fin n → ℝ) :
    conjTorus z (1 : Langlands.GeneralLinear.upperUnipotent n ℝ) = 1 := by
  apply Subtype.ext
  change torus z * (1 : Langlands.GeneralLinear n ℝ) * torus (-z) = 1
  rw [mul_one, torus_neg, mul_inv_cancel]

/-! ### Quasi-invariant measures on `ℝⁿ` -/

section Haar

theorem exists_integral_ne_zero {ρ : Measure (Fin n → ℝ)} [IsFiniteMeasureOnCompacts ρ]
    (hρ : ρ ≠ 0) : ∃ φ : C_c(Fin n → ℝ, ℝ), ∫ x, φ x ∂ρ ≠ 0 := by
  by_contra H
  push Not at H
  apply hρ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [H f, integral_zero_measure]

/-- A nonzero measure on `ℝⁿ`, finite on compact sets, whose translates are positive multiples
`e z` of it (tested on compactly supported continuous functions) has `e = exp ∘ L` for a
linear form `L`. -/
theorem exists_linear_of_quasiInvariant (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasureOnCompacts ρ]
    (hρ : ρ ≠ 0) (e : (Fin n → ℝ) → ℝ) (he : ∀ z, 0 < e z)
    (h : ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      ∀ z, ∫ x, φ (z + x) ∂ρ = e z * ∫ x, φ x ∂ρ) :
    ∃ L : (Fin n → ℝ) →L[ℝ] ℝ, ∀ z, e z = Real.exp (L z) := by
  obtain ⟨φ, hφ⟩ := exists_integral_ne_zero hρ
  have hmul : ∀ z w, e (z + w) = e z * e w := by
    intro z w
    have h1 := h φ φ.continuous φ.hasCompactSupport (z + w)
    have h2 : ∫ x, φ (w + (z + x)) ∂ρ = e z * ∫ x, φ (w + x) ∂ρ :=
      h (fun x => φ (w + x)) (φ.continuous.comp (continuous_const.add continuous_id))
        (φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft w)) z
    have h3 := h φ φ.continuous φ.hasCompactSupport w
    have h4 : ∫ x, φ (z + w + x) ∂ρ = ∫ x, φ (w + (z + x)) ∂ρ := by
      congr 1
      funext x
      congr 1
      abel
    rw [h4, h2, h3] at h1
    exact mul_right_cancel₀ hφ (h1.symm.trans (mul_assoc _ _ _).symm)
  have hI : ∀ z, e z = (∫ x, φ (z + x) ∂ρ) / ∫ x, φ x ∂ρ := fun z => by
    rw [h φ φ.continuous φ.hasCompactSupport z, mul_div_assoc, div_self hφ, mul_one]
  have hmeas : Measurable e := by
    have hF : StronglyMeasurable fun z : Fin n → ℝ => ∫ x, φ (z + x) ∂ρ :=
      StronglyMeasurable.integral_prod_right (f := fun z x => φ (z + x))
        (by apply Continuous.stronglyMeasurable; exact φ.continuous.comp continuous_add)
    have he' : e = fun z => (∫ x, φ (z + x) ∂ρ) / ∫ x, φ x ∂ρ := funext hI
    rw [he']
    exact hF.measurable.div_const _
  let ℓ : (Fin n → ℝ) →+ ℝ := AddMonoidHom.mk' (fun z => Real.log (e z)) fun z w => by
    rw [hmul, Real.log_mul (he z).ne' (he w).ne']
  have hℓ : Continuous ℓ := ℓ.continuous_of_measurable (Real.measurable_log.comp hmeas)
  refine ⟨ℓ.toRealLinearMap hℓ, fun z => ?_⟩
  rw [AddMonoidHom.coe_toRealLinearMap]
  exact (Real.exp_log (he z)).symm

theorem measurable_exp_linear (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    Measurable fun x => ENNReal.ofReal (Real.exp (L x)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp L.continuous.measurable)

/-- If the translates of `ρ` are the multiples `exp (L z)` of `ρ`, then the density
`exp ∘ L` turns `ρ` into a translation-invariant measure, a multiple of Lebesgue measure. -/
theorem withDensity_eq_smul_volume (ρ : Measure (Fin n → ℝ)) [IsFiniteMeasureOnCompacts ρ]
    (L : (Fin n → ℝ) →L[ℝ] ℝ)
    (h : ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      ∀ z, ∫ x, φ (z + x) ∂ρ = Real.exp (L z) * ∫ x, φ x ∂ρ) :
    ∃ κ : ℝ≥0, ρ.withDensity (fun x => ENNReal.ofReal (Real.exp (L x))) = κ • volume := by
  set ρ' := ρ.withDensity (fun x => ENNReal.ofReal (Real.exp (L x))) with hρ'
  have : IsLocallyFiniteMeasure ρ' :=
    IsLocallyFiniteMeasure.withDensity_ofReal (Real.continuous_exp.comp L.continuous)
  have hint : ∀ g : (Fin n → ℝ) → ℝ, ∫ x, g x ∂ρ' = ∫ x, Real.exp (L x) * g x ∂ρ := by
    intro g
    rw [hρ', integral_withDensity_eq_integral_toReal_smul (measurable_exp_linear L)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have : IsAddLeftInvariant ρ' := by
    refine ⟨fun z => ?_⟩
    have : IsFiniteMeasureOnCompacts (map (z + ·) ρ') :=
      IsFiniteMeasureOnCompacts.map ρ' (Homeomorph.addLeft z)
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (f := fun x => f x) (measurable_const_add z).aemeasurable
      (map_continuous f).aestronglyMeasurable]
    simp only [hint]
    let ψ : (Fin n → ℝ) → ℝ := fun y => Real.exp (-L z) * (Real.exp (L y) * f y)
    have hψc : Continuous ψ :=
      continuous_const.mul ((Real.continuous_exp.comp L.continuous).mul f.continuous)
    have hψ : HasCompactSupport ψ := f.hasCompactSupport.mul_left.mul_left
    have h2 : ∫ x, Real.exp (L x) * f (z + x) ∂ρ = ∫ x, ψ (z + x) ∂ρ := by
      congr 1
      funext x
      show _ = Real.exp (-L z) * (Real.exp (L (z + x)) * f (z + x))
      rw [map_add L z x, Real.exp_add, Real.exp_neg, mul_assoc (Real.exp (L z)),
        inv_mul_cancel_left₀ (Real.exp_pos _).ne']
    rw [h2, h ψ hψc hψ z, integral_const_mul, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, one_mul]
  exact ⟨_, isAddLeftInvariant_eq_smul ρ' volume⟩

theorem lintegral_eq_of_withDensity_eq (ρ : Measure (Fin n → ℝ)) (L : (Fin n → ℝ) →L[ℝ] ℝ)
    (κ : ℝ≥0) (hκ : ρ.withDensity (fun x => ENNReal.ofReal (Real.exp (L x))) = κ • volume)
    {B : (Fin n → ℝ) → ℝ≥0∞} (hB : Measurable B) :
    ∫⁻ x, B x ∂ρ = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (-L x)) * B x := by
  have hdm' : Measurable fun x => ENNReal.ofReal (Real.exp (-L x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp L.continuous.measurable.neg)
  have h1 : ∫⁻ x, B x ∂ρ = ∫⁻ x, ENNReal.ofReal (Real.exp (-L x)) * B x
      ∂(ρ.withDensity fun x => ENNReal.ofReal (Real.exp (L x))) := by
    rw [lintegral_withDensity_eq_lintegral_mul ρ (measurable_exp_linear L)
      (g := fun x => ENNReal.ofReal (Real.exp (-L x)) * B x) (hdm'.mul hB)]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one, one_mul]
  rw [h1, hκ, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

end Haar

/-! ### The Weil formula for lifted functions -/

section Weil

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  [MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ)] [BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ)]
  [MeasurableSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]
  [BorelSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]

variable (μG : Measure (Langlands.GeneralLinear n ℝ)) (μN : Measure (Langlands.GeneralLinear.upperUnipotent n ℝ))
  [IsMulRightInvariant μN] (ν : Measure (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ)))

omit [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  [MeasurableSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]
  [BorelSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))] in
theorem quotientAverage_lift (φ : (Fin n → ℝ) → ℝ) (β : Langlands.GeneralLinear.upperUnipotent n ℝ → ℝ) :
    quotientAverage (Langlands.GeneralLinear.upperUnipotent n ℝ) μN
        (fun g => ((φ (alpha g) * β (npart g) : ℝ) : ℂ)) =
      fun q => ((φ (alphaQ q) * ∫ h, β h ∂μN : ℝ) : ℂ) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Langlands.QuotientIntegration.quotientAverage_mk, alphaQ_mk]
    simp_rw [alpha_unipotent_mul, npart_unipotent_mul]
    rw [integral_complex_ofReal, integral_const_mul,
      integral_mul_right_eq_self (μ := μN) (fun h => β h) (npart g)]

omit [BorelSpace (Langlands.GeneralLinear n ℝ)]
  [BorelSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))] in
theorem weil_lift (hν : Langlands.QuotientIntegration.IsCompatible (Langlands.GeneralLinear.upperUnipotent n ℝ) μG μN ν)
    {φ : (Fin n → ℝ) → ℝ} {β : Langlands.GeneralLinear.upperUnipotent n ℝ → ℝ} (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (hβc : Continuous β) (hβ : HasCompactSupport β) :
    (∫ q, φ (alphaQ q) ∂ν) * ∫ h, β h ∂μN = ∫ g, φ (alpha g) * β (npart g) ∂μG := by
  have hf := hν.integral_formula (fun g => ((φ (alpha g) * β (npart g) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_lift hφc hβc))
    ((hasCompactSupport_lift hφ hβ).comp_left Complex.ofReal_zero)
  rw [quotientAverage_lift] at hf
  simp only [integral_complex_ofReal] at hf
  have h := Complex.ofReal_injective hf
  rwa [integral_mul_const] at h

omit [BorelSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))] in
theorem weil_translate [IsMulLeftInvariant μG]
    (hν : Langlands.QuotientIntegration.IsCompatible (Langlands.GeneralLinear.upperUnipotent n ℝ) μG μN ν)
    {φ : (Fin n → ℝ) → ℝ} {β : Langlands.GeneralLinear.upperUnipotent n ℝ → ℝ} (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (hβc : Continuous β) (hβ : HasCompactSupport β)
    (z : Fin n → ℝ) :
    (∫ q, φ (z + alphaQ q) ∂ν) * (∫ h, β (conjTorus z h) ∂μN) =
      (∫ q, φ (alphaQ q) ∂ν) * ∫ h, β h ∂μN := by
  have hφz : HasCompactSupport fun x => φ (z + x) :=
    hφ.comp_homeomorph (Homeomorph.addLeft z)
  have hβz : HasCompactSupport fun h => β (conjTorus z h) :=
    hβ.comp_homeomorph (conjTorusHomeomorph z)
  have h1 := weil_lift μG μN ν hν (φ := fun x => φ (z + x)) (β := fun h => β (conjTorus z h))
    (hφc.comp (continuous_const.add continuous_id)) hφz
    (hβc.comp (continuous_conjTorus_right z)) hβz
  have h2 := weil_lift μG μN ν hν hφc hφ hβc hβ
  rw [h1, h2, ← integral_mul_left_eq_self (μ := μG)
    (fun g => φ (alpha g) * β (npart g)) (torus z)]
  simp_rw [alpha_torus_mul, npart_torus_mul]

/-- The translates of the toral pushforward of a compatible quotient measure are positive
multiples of it. -/
theorem exists_quasiInvariant [IsMulLeftInvariant μG] [IsHaarMeasure μN]
    (hν : Langlands.QuotientIntegration.IsCompatible (Langlands.GeneralLinear.upperUnipotent n ℝ)
      μG μN ν) :
    ∃ e : (Fin n → ℝ) → ℝ, (∀ z, 0 < e z) ∧ ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ →
      HasCompactSupport φ →
        ∀ z, ∫ x, φ (z + x) ∂(ν.map alphaQ) = e z * ∫ x, φ x ∂(ν.map alphaQ) := by
  obtain ⟨β, hβc, hβ, hβ0, hβ1⟩ := exists_unipotent_bump (n := n)
  have hc : ∀ z : Fin n → ℝ, 0 < ∫ h, β (conjTorus z h) ∂μN := fun z =>
    (hβc.comp (continuous_conjTorus_right z)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hβ.comp_homeomorph (conjTorusHomeomorph z)) (fun h => hβ0 _) (x := 1)
      (by simp only [conjTorus_one, hβ1]; exact one_ne_zero)
  have hc0 : 0 < ∫ h, β h ∂μN :=
    hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hβ (fun h => hβ0 h) (x := 1)
      (by rw [hβ1]; exact one_ne_zero)
  refine ⟨fun z => (∫ h, β h ∂μN) / ∫ h, β (conjTorus z h) ∂μN, fun z => div_pos hc0 (hc z), ?_⟩
  intro φ hφc hφ z
  have hw := weil_translate μG μN ν hν hφc hφ hβc hβ z
  have h1 : ∫ x, φ (z + x) ∂(ν.map alphaQ) = ∫ q, φ (z + alphaQ q) ∂ν :=
    integral_map_alphaQ ν (φ := fun x => φ (z + x)) (hφc.comp (continuous_const.add continuous_id))
  rw [h1, integral_map_alphaQ ν hφc]
  show _ = (∫ h, β h ∂μN) / (∫ h, β (conjTorus z h) ∂μN) * _
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff (hc z).ne', hw]
  ring

/-- **Integration in the toral coordinate.** For a compatible quotient measure `ν` on
`N \ GL_n(ℝ)` there are a constant `κ ≥ 0` and a linear form `L` on `ℝⁿ` such that
`∫ B (alphaQ q) dν(q) = κ ∫ B(x) exp(L x) dx` for every measurable `B ≥ 0`. -/
theorem exists_lintegral_alphaQ [IsMulLeftInvariant μG] [IsHaarMeasure μN]
    (hν : Langlands.QuotientIntegration.IsCompatible (Langlands.GeneralLinear.upperUnipotent n ℝ)
      μG μN ν) :
    ∃ (κ : ℝ≥0) (L : (Fin n → ℝ) →L[ℝ] ℝ), ∀ B : (Fin n → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x := by
  have := hν.regular
  have := isFiniteMeasureOnCompacts_map_alphaQ ν
  obtain ⟨e, he, hq⟩ := exists_quasiInvariant μG μN ν hν
  have hρ : ν.map alphaQ ≠ 0 := by
    intro h0
    apply hν.nonzero
    rwa [Measure.map_eq_zero_iff measurable_alphaQ.aemeasurable] at h0
  obtain ⟨L, hL⟩ := exists_linear_of_quasiInvariant (ν.map alphaQ) hρ e he hq
  have hL' : ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      ∀ z, ∫ x, φ (z + x) ∂(ν.map alphaQ) = Real.exp (L z) * ∫ x, φ x ∂(ν.map alphaQ) := by
    intro φ hφc hφ z
    rw [hq φ hφc hφ z, hL z]
  obtain ⟨κ, hκ⟩ := withDensity_eq_smul_volume _ L hL'
  refine ⟨κ, -L, fun B hB => ?_⟩
  rw [← lintegral_map hB measurable_alphaQ, lintegral_eq_of_withDensity_eq _ L κ hκ hB]
  simp only [_root_.neg_apply]

end Weil

end Langlands.Global.RankinSelbergGlobal.RealIwasawa
