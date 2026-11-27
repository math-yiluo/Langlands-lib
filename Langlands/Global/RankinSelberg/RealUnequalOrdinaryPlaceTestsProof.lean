import Langlands.Global.RankinSelberg.RealWhittakerTranslateProjection
import Langlands.Global.RankinSelberg.RealUnequalLastRowDescent
import Langlands.Global.RankinSelberg.RealUnequalRankZeroOrdinary
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial

/-! # Ordinary nonvanishing for unequal ranks at a real place

Proof of `RealUnequalOrdinaryPlaceTestsStatement`. If all ordinary integrals of actual
restrictions vanished on right half-planes, vanishing would pass to genuine right translates
(compact projection and polynomial density on `O(n)`), then down the last rows of the smaller group
(`RealUnequalLastRowDescentStatement`) to `GL₁`, where the Mellin argument of the module
`RealUnequalRankZeroOrdinary` forces the product of the identity values to vanish. See the paired
Markdown.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

namespace RealUnequalTranslateVanishing

open Langlands.Archimedean (unitaryCompact continuous_unitary_toUnits matrixModel)
open Langlands.Archimedean.OrthogonalFinitePolynomial (polynomialStar polynomialStar_toSubalgebra
  inv_mul_mem_separated separated eq_zero_of_integral_polynomial_mul_eq_zero)
open RealWhittakerTranslateProjection (IsRealCoefficientMap)
open ArchimedeanLocal Langlands.LocalFactor.Archimedean

attribute [local instance] translateProjectionMeasurable' translateProjectionBorel'

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "U" => fun n => unitaryCompact ℝ n

/-! ### Polynomial weights in matrix coordinates -/

/-- The orthogonal matrices as the orthogonal subgroup of the invertible matrices. -/
def compactEquiv (n : ℕ) : K n ≃* U n where
  toFun k := ⟨Unitary.toUnits k, k.2⟩
  invFun k := ⟨k.val.val, k.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Units.ext rfl)
  map_mul' k l := Subtype.ext (Unitary.toUnits.map_mul k l)

theorem continuous_compactEquiv (n : ℕ) : Continuous (compactEquiv n) :=
  continuous_unitary_toUnits.subtype_mk _

theorem continuous_compactEquiv_symm (n : ℕ) : Continuous (compactEquiv n).symm :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

/-- A polynomial weight has finite-dimensional span of left translates. -/
theorem polynomial_finiteLeftSpan {n : ℕ} (w : C(K n, ℂ)) (hw : w ∈ polynomialStar n) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun x : K n => fun k => w (x⁻¹ * k))) := by
  have hw' : w ∈ (polynomialStar n).toSubalgebra := hw
  rw [polynomialStar_toSubalgebra] at hw'
  have hsep := inv_mul_mem_separated hw'
  rw [separated] at hsep
  obtain ⟨m, c, s, hs⟩ := Submodule.mem_span_set'.mp hsep
  choose α _ β hβ using fun i => (s i).property
  let β' (i : Fin m) : K n → ℂ := β i
  have hV : FiniteDimensional ℂ (Submodule.span ℂ (range β')) :=
    FiniteDimensional.span_of_finite ℂ (finite_range β')
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (range β'))
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  change (fun k => w (x⁻¹ * k)) ∈ Submodule.span ℂ (range β')
  have hrep : (fun k => w (x⁻¹ * k)) = ∑ i, (c i * α i x) • β' i := by
    funext k
    have hh := (congrFun (congrFun hs x) k).symm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh ⊢
    simp_rw [hβ, ← mul_assoc] at hh
    exact hh
  rw [hrep]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The compact projection of a genuine right translate, with a polynomial weight in matrix
coordinates and any Haar measure on `O(n)`. -/
theorem exists_polynomial_projection {r : ℕ} {ds : List RealBlock}
    (μ : Measure (K (r + 1))) [μ.IsHaarMeasure]
    (w : C(K (r + 1), ℂ)) (hw : w ∈ polynomialStar (r + 1))
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)}
    (hB : IsRealCoefficientMap B) (f : Automorphic.realStandardKFinite (r + 1) ds)
    (g : G (r + 1)) :
    ∃ p : Automorphic.realStandardKFinite (r + 1) ds,
      (∀ x : G (r + 1), p.val x = ∫ k : K (r + 1), w k * f.val (x * Unitary.toUnits k * g) ∂μ) ∧
      ∀ x : G (r + 1), B p x = ∫ k : K (r + 1), w k * B f (x * Unitary.toUnits k * g) ∂μ := by
  let n := r + 1
  let e := compactEquiv n
  let ν := μ.map e
  have he : Continuous e := continuous_compactEquiv n
  have hν : ν.IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure μ e.toMonoidHom he e.surjective
  let w' : C(U n, ℂ) := ⟨fun k => w (e.symm k), w.continuous.comp (continuous_compactEquiv_symm n)⟩
  let W : Submodule ℂ (K n → ℂ) := Submodule.span ℂ (range fun x : K n => fun k => w (x⁻¹ * k))
  have hW : FiniteDimensional ℂ W := polynomial_finiteLeftSpan w hw
  let P : (K n → ℂ) →ₗ[ℂ] (U n → ℂ) := LinearMap.pi fun k => LinearMap.proj (e.symm k)
  have hFin : FiniteDimensional ℂ
      (Submodule.span ℂ (range fun x : U n => fun k => w' (x⁻¹ * k))) := by
    apply Submodule.finiteDimensional_of_le (S₂ := W.map P)
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    refine ⟨fun k => w ((e.symm x)⁻¹ * k), Submodule.subset_span ⟨e.symm x, rfl⟩, ?_⟩
    funext k
    change w ((e.symm x)⁻¹ * e.symm k) = w (e.symm (x⁻¹ * k))
    rw [map_mul e.symm, map_inv e.symm]
  obtain ⟨p, hp, hBp⟩ := realWhittakerTranslateProjection r ds ν hν w' hFin B hB f g
  have transport {F : G n → ℂ} (hF : Continuous F) (x : G n) :
      (∫ k : U n, w' k * F (x * k.val * g) ∂ν) =
        ∫ k : K n, w k * F (x * Unitary.toUnits k * g) ∂μ := by
    have hc : Continuous (fun k : U n => w' k * F (x * k.val * g)) := w'.continuous.mul
      (hF.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    rw [integral_map he.measurable.aemeasurable hc.aestronglyMeasurable]
    apply integral_congr_ae (ae_of_all _ fun k => ?_)
    change w (e.symm (e k)) * F (x * Unitary.toUnits k * g) = _
    rw [e.symm_apply_apply]
  exact ⟨p, fun x => (hp x).trans
      (transport (Archimedean.contMDiff_of_mem_realStandardModule f.2.1).continuous x),
    fun x => (hBp x).trans (transport (hB.1 f).continuous x)⟩


/-! ### Vanishing for genuine right translates -/

section Transfer

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

open RealUnequalFamily (HasLeftCharacter HasUniformGauge ordinary_halfPlaneDomination
  continuous_integrand integrand_mk)
open ComplexUnequalFamily (HalfPlaneDomination differentiableOn_integral_of_halfPlaneDomination)
open RealLocalWhittaker (iteratedRightDerivative regularFunctions)
open RealUniformWhittaker (HasUniformDerivativeGrowth)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap leftQuotientMap_apply)

variable {r t : ℕ} (h : t < r)

local notation "ρ" => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)

theorem hasLeftCharacter_translate {a : ℝˣ} {W : G (r + 1) → ℂ} (hW : HasLeftCharacter a W)
    (c : G (r + 1)) : HasLeftCharacter a (ρ c W) := by
  intro u hu x
  change W (u * x * c) = _ * W (x * c)
  rw [mul_assoc]
  exact hW u hu (x * c)

/-- The ordinary integrand of an average of right translates is the average of the integrands. -/
theorem integrand_average {μ : Measure (K (r + 1))} {W W' : G (r + 1) → ℂ} {V : G (t + 1) → ℂ}
    {w : K (r + 1) → ℂ} {g : G (r + 1)}
    (hW' : ∀ x, W' x = ∫ k, w k * W (x * Unitary.toUnits k * g) ∂μ) (s : ℂ)
    (q : LeftUnipotentQuotient t ℝ) :
    realUnequalIntegrand h W' V s q =
      ∫ k, w k * realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s q ∂μ := by
  change W' _ * V _ * _ = ∫ k, w k * (W (_ * (Unitary.toUnits k * g)) * V _ * _) ∂μ
  rw [hW', ← integral_mul_const, ← integral_mul_const]
  congr 1
  funext k
  rw [mul_assoc (padGL _ _ : G (r + 1))]
  ring


set_option maxHeartbeats 2000000 in
/-- **Transfer of vanishing to a genuine right translate.** Suppose that for every polynomial
weight `w` on `O(r+1)` the average `x ↦ ∫ w(k) W(x k g) dμ(k)` has an ordinary integral with `V`
vanishing on a right half-plane. Then so does the right translate of `W` by `g`. -/
theorem translate_vanishing (D : RealQuotientMeasureData t) {a : ℝˣ} {W : G (r + 1) → ℂ}
    (hW : HasLeftCharacter a W) (hWc : Continuous W)
    (hWg : RealWhittakerTranslatedMellin.HasGaugeBound W) {V : G (t + 1) → ℂ}
    (hV : HasLeftCharacter (-a) V) (hVc : Continuous V)
    (hVg : HasUniformGauge (univ : Set Unit) (fun _ => V))
    (μ : Measure (K (r + 1))) [μ.IsHaarMeasure] (g : G (r + 1))
    (havg : ∀ w ∈ polynomialStar (r + 1), ∃ W' : G (r + 1) → ℂ,
      (∀ x, W' x = ∫ k, w k * W (x * Unitary.toUnits k * g) ∂μ) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realUnequalIntegral h D W' V s = 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realUnequalIntegral h D (ρ g W) V s = 0 := by
  have : SigmaFinite D.measure := RealUnequalLastRowDescent.sigmaFinite_measure D
  have hTc (c : G (r + 1)) : Continuous (ρ c W) :=
    hWc.comp (continuous_id.mul continuous_const)
  set S : Set (G (r + 1)) := range (fun k : K (r + 1) => Unitary.toUnits k * g)
  have hS : IsCompact S := isCompact_range (continuous_unitary_toUnits.mul continuous_const)
  have hgS := RealWhittakerTranslatedMellin.compact_rightTranslate_uniformGauge hWg S hS
  let S' : Set (G (r + 1) × ℂ) := S ×ˢ univ
  let Wf : G (r + 1) × ℂ → G (r + 1) → ℂ := fun p => ρ p.1 W
  let Vf : G (r + 1) × ℂ → G (t + 1) → ℂ := fun _ => V
  have hWb : HasUniformGauge S' Wf := by
    obtain ⟨N, hN⟩ := hgS
    exact ⟨N, fun M => by
      obtain ⟨C, hC, hb⟩ := hN M
      exact ⟨C, hC, fun p hp => hb p.1 hp.1⟩⟩
  have hVb : HasUniformGauge S' Vf := by
    obtain ⟨N, hN⟩ := hVg
    exact ⟨N, fun M => by
      obtain ⟨C, hC, hb⟩ := hN M
      exact ⟨C, hC, fun _ _ => hb () (mem_univ _)⟩⟩
  obtain ⟨σ₀, hdom⟩ := ordinary_halfPlaneDomination h D S' Wf Vf Prod.snd
    (fun p => hasLeftCharacter_translate hW p.1) (fun _ => hV) hWb hVb
  have hmem (k : K (r + 1)) (s : ℂ) : (Unitary.toUnits k * g, s) ∈ S' :=
    ⟨⟨k, rfl⟩, mem_univ _⟩
  have hjoint (s : ℂ) : Continuous (Function.uncurry fun (q : LeftUnipotentQuotient t ℝ)
      (k : K (r + 1)) => realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s q) := by
    have hq : IsOpenQuotientMap (Prod.map (Langlands.QuotientIntegration.leftQuotientMap
        (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ)) (id : K (r + 1) → K (r + 1))) :=
      (leftQuotient_isOpenQuotientMap _).prodMap IsOpenQuotientMap.id
    apply hq.isQuotientMap.continuous_iff.mpr
    have he : (Function.uncurry fun (q : LeftUnipotentQuotient t ℝ) (k : K (r + 1)) =>
        realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s q) ∘
          Prod.map (Langlands.QuotientIntegration.leftQuotientMap
            (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ)) id =
        fun p : G (t + 1) × K (r + 1) =>
          W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) p.1 * (Unitary.toUnits p.2 * g)) * V p.1 *
            Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (RealEqualConvergence.logDet p.1 : ℂ)) := by
      funext p
      change realUnequalIntegrand h (ρ (Unitary.toUnits p.2 * g) W) V s
        (Langlands.QuotientIntegration.leftQuotientMap _ p.1) = _
      rw [leftQuotientMap_apply, integrand_mk h (hasLeftCharacter_translate hW _) hV]
      rfl
    rw [he]
    exact ((hWc.comp (((UnequalAnalytic.continuous_padGL _).comp continuous_fst).mul
      ((continuous_unitary_toUnits.comp continuous_snd).mul continuous_const))).mul
      (hVc.comp continuous_fst)).mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (RealEqualConvergence.continuous_logDet.comp
          continuous_fst))))
  have hslice (s : ℂ) (q : LeftUnipotentQuotient t ℝ) :
      Continuous (fun k : K (r + 1) =>
        realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s q) :=
    (hjoint s).uncurry_left q
  have hbound (s : ℂ) (hs : σ₀ < s.re) : ∃ B : LeftUnipotentQuotient t ℝ → ℝ,
      Integrable B D.measure ∧ ∀ (k : K (r + 1)) (q : LeftUnipotentQuotient t ℝ),
        ‖realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s q‖ ≤ B q := by
    obtain ⟨B, hBi, hBb⟩ := hdom s.re
    exact ⟨B, hBi, fun k q => hBb (Unitary.toUnits k * g, s) (hmem k s) hs le_rfl q⟩
  have hmeas (s : ℂ) (k : K (r + 1)) :
      AEStronglyMeasurable (realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s)
        D.measure :=
    (continuous_integrand h (hasLeftCharacter_translate hW _) hV (hTc _) hVc s).aestronglyMeasurable
  have hcontI (s : ℂ) (hs : σ₀ < s.re) : Continuous (fun k : K (r + 1) =>
      realUnequalIntegral h D (ρ (Unitary.toUnits k * g) W) V s) := by
    obtain ⟨B, hBi, hBb⟩ := hbound s hs
    exact continuous_of_dominated (hmeas s) (fun k => ae_of_all _ (hBb k)) hBi
      (ae_of_all _ (hslice s))
  have hpoly (w : C(K (r + 1), ℂ)) (hw : w ∈ polynomialStar (r + 1)) (s : ℂ) (hs : σ₀ < s.re) :
      ∫ k, w k * realUnequalIntegral h D (ρ (Unitary.toUnits k * g) W) V s ∂μ = 0 := by
    obtain ⟨W', hW'eq, σw, hzero⟩ := havg w hw
    have hfub (s' : ℂ) (hs' : σ₀ < s'.re) :
        realUnequalIntegral h D W' V s' =
          ∫ k, w k * realUnequalIntegral h D (ρ (Unitary.toUnits k * g) W) V s' ∂μ := by
      obtain ⟨B, hBi, hBb⟩ := hbound s' hs'
      let Φ : LeftUnipotentQuotient t ℝ → K (r + 1) → ℂ := fun q k =>
        w k * realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s' q
      have hΦc : Continuous (Function.uncurry Φ) :=
        (w.continuous.comp continuous_snd).mul (hjoint s')
      have hmeasP : AEStronglyMeasurable (Function.uncurry Φ) (D.measure.prod μ) :=
        hΦc.aestronglyMeasurable
      have hint : Integrable (Function.uncurry Φ) (D.measure.prod μ) := by
        refine Integrable.mono' (hBi.mul_prod (integrable_const ‖w‖)) hmeasP
          (ae_of_all _ fun p => ?_)
        change ‖w p.2 * realUnequalIntegrand h (ρ (Unitary.toUnits p.2 * g) W) V s' p.1‖ ≤
          B p.1 * ‖w‖
        rw [norm_mul]
        calc ‖w p.2‖ * ‖realUnequalIntegrand h (ρ (Unitary.toUnits p.2 * g) W) V s' p.1‖
            ≤ ‖w‖ * B p.1 :=
              mul_le_mul (w.norm_coe_le_norm p.2) (hBb p.2 p.1) (norm_nonneg _)
                (norm_nonneg _)
          _ = B p.1 * ‖w‖ := mul_comm _ _
      change ∫ q, realUnequalIntegrand h W' V s' q ∂D.measure = _
      simp_rw [integrand_average h hW'eq s']
      rw [integral_integral_swap (f := Φ) hint]
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      exact integral_const_mul _ _
    have hhol : DifferentiableOn ℂ (fun s' => realUnequalIntegral h D W' V s')
        {s' : ℂ | σ₀ < s'.re} := by
      have hdomW : HalfPlaneDomination D.measure (univ : Set ℂ) id
          (fun s' q => realUnequalIntegrand h W' V s' q) σ₀ := by
        intro τ
        obtain ⟨B, hBi, hBb⟩ := hdom τ
        refine ⟨fun q => ‖w‖ * (μ univ).toReal * B q, hBi.const_mul (‖w‖ * (μ univ).toReal),
          fun s' _ hs' hτ q => ?_⟩
        show ‖realUnequalIntegrand h W' V s' q‖ ≤ ‖w‖ * (μ univ).toReal * B q
        rw [integrand_average h hW'eq s']
        refine (norm_integral_le_of_norm_le_const (C := ‖w‖ * B q)
          (ae_of_all _ fun k => ?_)).trans (le_of_eq ?_)
        · rw [norm_mul]
          exact mul_le_mul (w.norm_coe_le_norm k)
            (hBb (Unitary.toUnits k * g, s') (hmem k s') hs' hτ q) (norm_nonneg _)
            (norm_nonneg _)
        · rw [Measure.real]
          ring
      have hmeasW (s' : ℂ) : AEStronglyMeasurable (realUnequalIntegrand h W' V s') D.measure := by
        have hm : AEStronglyMeasurable (fun q : LeftUnipotentQuotient t ℝ =>
            ∫ k, w k * realUnequalIntegrand h (ρ (Unitary.toUnits k * g) W) V s' q ∂μ)
            D.measure :=
          ((w.continuous.comp continuous_snd).mul (hjoint s')).aestronglyMeasurable
            |>.integral_prod_right'
        exact hm.congr (ae_of_all _ fun q => (integrand_average h hW'eq s' q).symm)
      have hdiff (q : LeftUnipotentQuotient t ℝ) :
          DifferentiableOn ℂ (fun s' => realUnequalIntegrand h W' V s' q) (univ : Set ℂ) := by
        change DifferentiableOn ℂ (fun s' => W' _ * V _ *
          Complex.exp ((s' - ((r - t : ℕ) : ℂ) / 2) * _)) univ
        exact ((differentiable_const _).mul (Complex.differentiable_exp.comp
          ((differentiable_id.sub_const _).mul_const _))).differentiableOn
      have hd := (differentiableOn_integral_of_halfPlaneDomination isOpen_univ differentiable_id
        hmeasW hdiff hdomW).2
      rw [univ_inter] at hd
      convert hd using 1 <;> rfl
    rw [← hfub s hs]
    exact RealUnequalLastRowDescent.eq_zero_on_right hhol (τ := max σ₀ σw)
      (fun s' hs' => hzero s' ((le_max_right _ _).trans_lt hs')) s hs
  refine ⟨σ₀, fun s hs => ?_⟩
  let gf : C(K (r + 1), ℂ) := ⟨fun k => realUnequalIntegral h D (ρ (Unitary.toUnits k * g) W) V s,
    hcontI s hs⟩
  have h0 := eq_zero_of_integral_polynomial_mul_eq_zero μ gf (fun φ hφ => hpoly φ hφ s hs)
  have h1 := congrArg (fun F : C(K (r + 1), ℂ) => F 1) h0
  simpa only [gf, ContinuousMap.coe_mk, ContinuousMap.zero_apply, map_one, one_mul] using h1


/-- For a real Whittaker intertwiner `B` whose values have simple-root gauge bounds, if the
ordinary integral of every `B f` against `V` vanishes on a right half-plane, then so does that of
every genuine right translate of every `B f`. -/
theorem translate_vanishing_of_intertwiner (D : RealQuotientMeasureData t) {a : ℝˣ}
    {ds : List RealBlock}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B)
    (hBg : ∀ f, RealWhittakerTranslatedMellin.HasGaugeBound (B f))
    {V : G (t + 1) → ℂ} (hV : HasLeftCharacter (-a) V) (hVc : Continuous V)
    (hVg : RealWhittakerTranslatedMellin.HasGaugeBound V)
    (hall : ∀ f, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realUnequalIntegral h D (B f) V s = 0)
    (f : Automorphic.realStandardKFinite (r + 1) ds) (g : G (r + 1)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral h D (fun x => B f (x * g)) V s = 0 := by
  let μ : Measure (K (r + 1)) := Measure.haar
  refine translate_vanishing h D (hB.1 f) (hB.2.1 f).continuous (hBg f) hV hVc
    (RealUnequalLastRowDescent.hasUniformGauge_const' hVg _) μ g (fun w hw => ?_)
  obtain ⟨p, -, hp⟩ := exists_polynomial_projection μ w hw
    (RealWhittakerTranslateProjection.isRealCoefficientMap_of_intertwiner hB) f g
  exact ⟨B p, hp, hall p⟩

end Transfer

end RealUnequalTranslateVanishing

/-! ### Iterated descent -/

namespace RealUnequalPositiveRank

open RealUnequalTranslateVanishing RealUnequalLastRowDescent ArchimedeanLocal
open RealUnequalFamily (HasLeftCharacter HasUniformGauge ordinary_halfPlaneDomination
  continuous_integrand)
open RealWhittakerTranslatedMellin (HasGaugeBound hasGaugeBound_of_mem_model)
open Langlands.LocalFactor.Archimedean

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

theorem padGL_refl {m : ℕ} (M : Langlands.GeneralLinear m ℝ) : padGL (le_refl m) M = M := by
  apply Units.ext
  ext i j
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨i.isLt, j.isLt⟩]

theorem hasLeftCharacter_padGL {k t : ℕ} (hk : k ≤ t) {a : ℝˣ}
    {V : Langlands.GeneralLinear (t + 1) ℝ → ℂ} (hV : HasLeftCharacter a V) :
    HasLeftCharacter a (fun z : Langlands.GeneralLinear (k + 1) ℝ =>
      V (padGL (Nat.succ_le_succ hk) z)) := by
  intro u hu z
  change V (padGL _ (u * z)) = _ * V (padGL _ z)
  rw [map_mul, hV _ (RealUnequalConvergence.padGL_mem_upperUnipotent _ hu)]
  rcases hk.lt_or_eq with hlt | heq
  · rw [RealUnequalConvergence.realWhittakerCharacter_padGL hlt]
  · subst heq
    rw [padGL_refl]

theorem hasGaugeBound_padGL {k t : ℕ} (hk : k ≤ t) {V : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hV : HasGaugeBound V) :
    HasGaugeBound (fun z : Langlands.GeneralLinear (k + 1) ℝ =>
      V (padGL (Nat.succ_le_succ hk) z)) := by
  rcases hk.lt_or_eq with hlt | heq
  · exact hasGaugeBound_pad hlt _ hV
  · subst heq
    simpa only [padGL_refl] using hV

/-- **Iterated descent.** If the ordinary integrals of all coefficients `B f` of a real Whittaker
intertwiner against a fixed `W'` on `GL_(t+1)(ℝ)` vanish on right half-planes, then so do their
ordinary integrals against the restriction of `W'` to `GL₁(ℝ)`. -/
theorem descent_to_rankZero {r t : ℕ} (h : t < r) {a : ℝˣ} {ds : List RealBlock}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (hBg : ∀ f, HasGaugeBound (B f))
    {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ} (hW' : HasLeftCharacter (-a) W')
    (hW'c : Continuous W') (hW'g : HasGaugeBound W')
    (htop : ∀ f, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral h (realQuotientMeasureData t) (B f) W' s = 0) :
    ∀ f, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral (Nat.lt_of_le_of_lt (Nat.zero_le t) h) (realQuotientMeasureData 0)
        (B f) (fun z => W' (padGL (Nat.succ_le_succ (Nat.zero_le t)) z)) s = 0 := by
  have claim : ∀ j k : ℕ, ∀ hk : k + j = t, ∀ f, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral (Nat.lt_of_le_of_lt (by omega : k ≤ t) h) (realQuotientMeasureData k)
        (B f) (fun z => W' (padGL (Nat.succ_le_succ (by omega : k ≤ t)) z)) s = 0 := by
    intro j
    induction j with
    | zero =>
      intro k hk f
      have hkt : k = t := by omega
      subst hkt
      simpa only [padGL_refl] using htop f
    | succ j ih =>
      intro k hk f
      have hk1 : k + 1 ≤ t := by omega
      have h' : k + 1 < r := lt_of_le_of_lt hk1 h
      let V : Langlands.GeneralLinear (k + 1 + 1) ℝ → ℂ := fun z =>
        W' (padGL (Nat.succ_le_succ hk1) z)
      have hVl : HasLeftCharacter (-a) V := hasLeftCharacter_padGL hk1 hW'
      have hVc : Continuous V := hW'c.comp (UnequalAnalytic.continuous_padGL _)
      have hVg : HasGaugeBound V := hasGaugeBound_padGL hk1 hW'g
      have hall := ih (k + 1) (by omega)
      have hvan : ∀ y : Fin (k + 1 + 1) → ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
          realUnequalIntegral h' (realQuotientMeasureData (k + 1))
            (fun x => B f (x * colUnip (r := r) y)) V s = 0 :=
        fun y => translate_vanishing_of_intertwiner h' (realQuotientMeasureData (k + 1)) hB hBg
          hVl hVc hVg hall f (colUnip y)
      obtain ⟨σ, hσ⟩ := lastRow_descent h' (realQuotientMeasureData k)
        (realQuotientMeasureData (k + 1)) (hB.1 f) hVl (hB.2.1 f).continuous hVc (hBg f) hVg hvan
      refine ⟨σ, fun s hs => ?_⟩
      have := hσ s hs
      simpa only [V, UnequalAnalytic.padGL_padGL] using this
  exact claim t 0 (Nat.zero_add t)

end RealUnequalPositiveRank

/-! ### Ordinary nonvanishing at a real place -/

open RealUnequalPositiveRank RealUnequalRankZero NumberField Automorphic HeckeFunctionalEquation
  ArchimedeanLocal
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (rightDerivative matrixModel)
open RealUnequalFamily (HasLeftCharacter ordinary_halfPlaneDomination continuous_integrand)
open RealWhittakerTranslatedMellin (HasGaugeBound hasGaugeBound_of_mem_model)
open scoped Classical CategoryTheory.MonObj

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanRealNMeasurable
  archimedeanRealNBorel

/-- Integrability of an ordinary integrand of gauged functions on a right half-plane. -/
theorem exists_integrable {r t : ℕ} (h : t < r) (D : RealQuotientMeasureData t) {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (hWc : Continuous W)
    (hVc : Continuous V) (hWg : HasGaugeBound W) (hVg : HasGaugeBound V) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W V s) D.measure := by
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination h D (Set.univ : Set ℂ) (fun _ => W)
    (fun _ => V) id (fun _ => hW) (fun _ => hV)
    (RealUnequalLastRowDescent.hasUniformGauge_const' hWg _)
    (RealUnequalLastRowDescent.hasUniformGauge_const' hVg _)
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨B, hBi, hB⟩ := hdom s.re
  exact hBi.mono' (continuous_integrand h hW hV hWc hVc s).aestronglyMeasurable
    (ae_of_all _ fun q => hB s (Set.mem_univ _) hs le_rfl q)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- **Ordinary nonvanishing at a real place.** For actual cuspidal realizations of
`GL_(r+1)` and `GL_(t+1)`, `t < r`, there are actual real-place Whittaker restrictions `W` for
`ψ` and `W'` for `ψ⁻¹` whose ordinary integral for `realQuotientMeasureData t` is nonzero
somewhere in every right half-plane. -/
theorem realUnequalOrdinaryPlaceTest
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) {r t : ℕ} (h : t < r)
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ) (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    (d d' : List RealBlock) (hd : T.realization.HasRealPlaceParameter v d)
    (hd' : T'.realization.HasRealPlaceParameter v d') :
    ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (D : RealQuotientMeasureData t),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realUnequalIntegral h D W W' s ≠ 0 := by
  have h0 : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le t) h
  obtain ⟨A, B, -, hB, ⟨f, hf⟩, hval⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).1 v d hd a ha
  set X := firstRootDirection h0
  let fX : realStandardKFinite (r + 1) d :=
    ⟨rightDerivative (matrixModel ℝ (r + 1)) X f,
      Archimedean.rightDerivative_mem_kFiniteFunctions_realStandardModule _ _ f.2 X⟩
  have hBX : B fX = rightDerivative (matrixModel ℝ (r + 1)) X (B f) := hB.2.2.2.2 X f fX rfl
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ := by
    rw [← complex_inverseCharacter]
    exact isStandardAdditiveCharacter_of_unitary _ (inverseCharacter_rational ψ hψ)
  obtain ⟨x', hx'⟩ := cuspidalWhittakerIdentityNonzero F t T' ψ.complex⁻¹ hstd'
  let W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ := fun g =>
    cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (t + 1) v g * finitePoint F (t + 1) 1)
  have hW'act : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' := ⟨x', 1, rfl⟩
  have hWact (g : realStandardKFinite (r + 1) d) :
      IsRealPlaceWhittaker F T ψ.complex v (B g) := by
    refine ⟨A g, 1, ?_⟩
    funext k
    rw [hval, mul_finitePoint_one]
  have hW'mem := (realPlaceUniformWhittakerModel F ψ hψ t T' v a ha d' hd' W').2 hW'act
  have hW'reg := realUniformWhittakerRegularity t d' (-a) W' hW'mem
  have hW'l : HasLeftCharacter (-a) W' := (hW'reg.1 []).1
  have hW'c : Continuous W' := (hW'reg.1 []).2.1.continuous
  have hW'g : HasGaugeBound W' := hasGaugeBound_of_mem_model hW'mem
  have hBg (g : realStandardKFinite (r + 1) d) : HasGaugeBound (B g) :=
    hasGaugeBound_of_mem_model ((realPlaceUniformWhittakerModel F ψ hψ r T v a ha d hd (B g)).1
      (hWact g))
  by_contra hcon
  push Not at hcon
  have htop (g : realStandardKFinite (r + 1) d) := hcon (B g) W' (realQuotientMeasureData t)
    (hWact g) hW'act
  have hall := descent_to_rankZero h hB hBg hW'l hW'c hW'g htop
  let V₀ : Langlands.GeneralLinear (0 + 1) ℝ → ℂ := fun z =>
    W' (padGL (Nat.succ_le_succ (Nat.zero_le t)) z)
  have hV₀l : HasLeftCharacter (-a) V₀ := hasLeftCharacter_padGL (Nat.zero_le t) hW'l
  have hV₀c : Continuous V₀ := hW'c.comp (UnequalAnalytic.continuous_padGL _)
  have hV₀g : HasGaugeBound V₀ := hasGaugeBound_padGL (Nat.zero_le t) hW'g
  obtain ⟨σa, hinta⟩ := exists_integrable h0 (realQuotientMeasureData 0) (hB.1 f) hV₀l
    (hB.2.1 f).continuous hV₀c (hBg f) hV₀g
  obtain ⟨σb, hintb⟩ := exists_integrable h0 (realQuotientMeasureData 0) (hB.1 fX) hV₀l
    (hB.2.1 fX).continuous hV₀c (hBg fX) hV₀g
  have hint (s : ℂ) (hs : max σa σb < s.re) :
      Integrable (realUnequalIntegrand h0 (B f) V₀ s) (realQuotientMeasureData 0).measure :=
    hinta s ((le_max_left _ _).trans_lt hs)
  have hintX (s : ℂ) (hs : max σa σb < s.re) :
      Integrable (realUnequalIntegrand h0 (rightDerivative (matrixModel ℝ (r + 1)) X (B f)) V₀ s)
        (realQuotientMeasureData 0).measure := by
    rw [← hBX]
    exact hintb s ((le_max_right _ _).trans_lt hs)
  obtain ⟨σ₁, hz⟩ := hall f
  obtain ⟨σ₂, hzX⟩ := hall fX
  rw [hBX] at hzX
  have hzero := value_eq_zero_of_integrals_eq_zero h0 (realQuotientMeasureData 0) (hB.2.1 f)
    (hB.1 f) hV₀c hint hintX hz hzX
  have hV₀1 : V₀ 1 = cuspWhittaker F T' ψ.complex⁻¹ x' 1 := by
    change cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (t + 1) v (padGL _ 1) *
      finitePoint F (t + 1) 1) = _
    rw [map_one, mul_finitePoint_one, realPlacePoint_one]
  rw [hf, one_mul, hV₀1] at hzero
  exact hx' hzero

/-- `RealUnequalOrdinaryPlaceTestsStatement` holds. -/
theorem realUnequalOrdinaryPlaceTests : RealUnequalOrdinaryPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T T' v a ha d d' hd hd'
  exact realUnequalOrdinaryPlaceTest ψ hψ h T T' v a ha d d' hd hd'

end Langlands.Global.RankinSelbergGlobal
