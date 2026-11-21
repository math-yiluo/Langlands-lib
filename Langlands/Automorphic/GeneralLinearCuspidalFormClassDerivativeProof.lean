import Langlands.Automorphic.GeneralLinearCuspidalFormClassDerivativeStatement
import Langlands.Automorphic.GroupSchemeFullAEL2Continuity
import Langlands.Global.AdelicGroupPolish
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Differentiation of the `L²` classes of cusp forms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj InnerProductSpace

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearFormClassDerivative

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.Automorphic

section Pointwise

open scoped Classical ContDiff Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

open ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "cX" => realLieExponentialCurve F n
local notation "E∞" => archimedeanGLCoordinates F n

private theorem exponentialCurve_matrix (X : RealLieAlgebra F n) (t : ℝ) :
    (E∞ (cX X t) : ArchimedeanMatrix F n) =
      NormedSpace.exp (t • realLieAlgebraToMatrix F n X) := by
  rw [realLieExponentialCurve, ContinuousMulEquiv.apply_symm_apply]
  rfl

private theorem continuous_exponentialCurve (X : RealLieAlgebra F n) :
    Continuous (cX X) := by
  apply (E∞).toHomeomorph.isEmbedding.continuous_iff.mpr
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · change Continuous (fun t : ℝ => (E∞ (cX X t) : ArchimedeanMatrix F n))
    simp_rw [exponentialCurve_matrix]
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  · change Continuous (fun t : ℝ => ((E∞ (cX X t)).inv : ArchimedeanMatrix F n))
    have h (t : ℝ) : (E∞ (cX X t)).inv =
        NormedSpace.exp (-(t • realLieAlgebraToMatrix F n X)) := by
      rw [realLieExponentialCurve, ContinuousMulEquiv.apply_symm_apply]
      rfl
    simp_rw [h]
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const).neg

private theorem smoothFunction_exponential_hasDerivAt (X : RealLieAlgebra F n)
    (f : SmoothFunctions F n) (a : InfiniteAdelicGL F n) (t : ℝ) :
    HasDerivAt (fun s => f.val (a * cX X s))
      ((smoothDifferential F n X f).val (a * cX X t)) t := by
  let M := realLieAlgebraToMatrix F n X
  let g (s : ℝ) := (E∞ (a * cX X s) : ArchimedeanMatrix F n)
  have hg (s : ℝ) : g s = (E∞ a : ArchimedeanMatrix F n) * NormedSpace.exp (s • M) := by
    simp only [g, map_mul, Units.val_mul, exponentialCurve_matrix, M]
  have hp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • M))
      (NormedSpace.exp (t • M) * M) t := hasDerivAt_exp_smul_const M t
  have h : HasDerivAt g (g t * M) t := by
    rw [funext hg]
    simpa only [mul_assoc] using hp.const_mul (E∞ a : ArchimedeanMatrix F n)
  have hF : HasFDerivAt (coordinateExtension F n f)
      (fderiv ℝ (coordinateExtension F n f) (g t)) (g t) :=
    (coordinateExtension_contDiffAt F n f (E∞ (a * cX X t))).differentiableAt
      (by simp) |>.hasFDerivAt
  have hc := hF.comp_hasDerivAt t h
  simp only [Function.comp_def, g, coordinateExtension_apply, ContinuousMulEquiv.symm_apply_apply]
    at hc
  exact hc

/-- Pointwise differentiation of the right orbit of a finite-smooth rational function. -/
theorem evaluate_exponential_hasDerivAt (X : RealLieAlgebra F n)
    (f : FiniteSmoothRationalFunctions F n) (x : AdelicGL F n) (t : ℝ) :
    HasDerivAt (fun s => Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n f.val (x * AdelicGL.ofInfinite F n (cX X s)))
      (Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n (finiteSmoothEnvelopingAction F n (envelopingGenerator F n
        (complexify F n X)) f).val (x * AdelicGL.ofInfinite F n (cX X t))) t := by
  let a := AdelicGL.infinite F n x
  let b := AdelicGL.finite F n x
  have hpair (s : ℝ) : x * AdelicGL.ofInfinite F n (cX X s) =
      AdelicGL.pair F n (a * cX X s) b := by
    rw [← AdelicGL.pair_projections F n x, AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]
  simp_rw [hpair]
  rw [evaluate_finiteSmoothEnvelopingAction, envelopingAction_real_generator_apply]
  exact smoothFunction_exponential_hasDerivAt F n X (finiteSmoothSlice F n b f) a t

end Pointwise

section Analysis

variable {A : Type*} [MeasurableSpace A] {m : Measure A}

private theorem integral_norm_sq (z : Lp ℂ 2 m) :
    (∫ x, ‖z x‖ ^ 2 ∂m) = ‖z‖ ^ 2 := by
  have h := integral_re (L2.integrable_inner (𝕜 := ℂ) z z)
  rw [← L2.inner_def (𝕜 := ℂ) z z] at h
  simpa only [inner_self_eq_norm_sq] using h

variable [SigmaFinite m]

private theorem integrable_prod_inner {ν : Measure ℝ} [IsFiniteMeasure ν]
    (z : Lp ℂ 2 m) (V : ℝ → Lp ℂ 2 m) (v : ℝ → A → ℂ) (C : ℝ)
    (hv : Measurable (Function.uncurry v)) (hV : ∀ t, (V t : A → ℂ) =ᵐ[m] v t)
    (hC : ∀ t, ‖V t‖ ≤ C) :
    Integrable (fun p : ℝ × A => ⟪z p.2, v p.1 p.2⟫_ℂ) (ν.prod m) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × A => ⟪z p.2, v p.1 p.2⟫_ℂ)
      (ν.prod m) :=
    ((Lp.stronglyMeasurable z).measurable.comp measurable_snd).aestronglyMeasurable.inner
      hv.aestronglyMeasurable
  have heq (t : ℝ) : (fun x => ⟪z x, V t x⟫_ℂ) =ᵐ[m] fun x => ⟪z x, v t x⟫_ℂ :=
    (hV t).mono fun x hx => congrArg (inner ℂ (z x)) hx
  refine (integrable_prod_iff hm).2 ⟨ae_of_all _ fun t =>
    (L2.integrable_inner (𝕜 := ℂ) z (V t)).congr (heq t), ?_⟩
  refine (integrable_const (‖z‖ ^ 2 + C ^ 2)).mono'
    (hm.norm.integral_prod_right') (ae_of_all _ fun t => ?_)
  change ‖∫ x, ‖⟪z x, v t x⟫_ℂ‖ ∂m‖ ≤ ‖z‖ ^ 2 + C ^ 2
  have hn : (∫ x, ‖⟪z x, V t x⟫_ℂ‖ ∂m) = ∫ x, ‖⟪z x, v t x⟫_ℂ‖ ∂m :=
    integral_congr_ae ((heq t).fun_comp norm)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hn]
  have hz : Integrable (fun x => ‖z x‖ ^ 2) m :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable z)).1 (Lp.memLp z)
  have hw : Integrable (fun x => ‖V t x‖ ^ 2) m :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (V t))).1 (Lp.memLp (V t))
  calc
    (∫ x, ‖⟪z x, V t x⟫_ℂ‖ ∂m) ≤ (∫ x, ‖z x‖ ^ 2 + ‖V t x‖ ^ 2 ∂m) :=
      integral_mono (L2.integrable_inner (𝕜 := ℂ) z (V t)).norm (hz.add hw) fun x =>
        (norm_inner_le_norm _ _).trans (by
          have h := two_mul_le_add_sq ‖z x‖ ‖V t x‖
          have h' := mul_nonneg (norm_nonneg (z x)) (norm_nonneg (V t x))
          linarith)
    _ = ‖z‖ ^ 2 + ‖V t‖ ^ 2 := by rw [integral_add hz hw, integral_norm_sq, integral_norm_sq]
    _ ≤ ‖z‖ ^ 2 + C ^ 2 := by gcongr; exact hC t

private theorem uncurry_continuous_section {A : Type*} [TopologicalSpace A]
    {v : ℝ → A → ℂ} (hv : Continuous (Function.uncurry v)) (q : A) :
    Continuous (fun t => v t q) :=
  hv.comp (continuous_id.prodMk continuous_const)

/-- A pointwise derivative with a bounded, norm-continuous `L²` class curve is the
norm derivative of the corresponding `L²` curve. -/
private theorem hasDerivAt_L2_of_pointwise
    (U V : ℝ → Lp ℂ 2 m) (u v : ℝ → A → ℂ) (C : ℝ)
    (hU : ∀ t, (U t : A → ℂ) =ᵐ[m] u t) (hV : ∀ t, (V t : A → ℂ) =ᵐ[m] v t)
    (hv : Measurable (Function.uncurry v)) (hvc : ∀ x, Continuous (fun t => v t x))
    (hVc : Continuous V) (hC : ∀ t, ‖V t‖ ≤ C)
    (hd : ∀ t x, HasDerivAt (fun s => u s x) (v t x) t) : HasDerivAt U (V 0) 0 := by
  have hFTC (t : ℝ) : U t - U 0 = ∫ s in (0 : ℝ)..t, V s := by
    refine ext_inner_left ℂ fun z => ?_
    let w (s : ℝ) (x : A) := ⟪z x, v s x⟫_ℂ
    have hwint (a b : ℝ) : Integrable (Function.uncurry w) ((volume.restrict (Set.Ioc a b)).prod m) :=
      integrable_prod_inner z V v C hv hV hC
    have hpoint (x : A) : (∫ s in (0 : ℝ)..t, w s x) = ⟪z x, u t x - u 0 x⟫_ℂ := by
      have he : (∫ s in (0 : ℝ)..t, v s x) = u t x - u 0 x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s x)
          ((hvc x).intervalIntegrable 0 t)
      rw [← he]
      exact (innerSL ℂ (z x)).intervalIntegral_comp_comm ((hvc x).intervalIntegrable 0 t)
    have hswap : (∫ s in (0 : ℝ)..t, ∫ x, w s x ∂m) = ∫ x, (∫ s in (0 : ℝ)..t, w s x) ∂m := by
      rw [intervalIntegral, integral_integral_swap (hwint 0 t),
        integral_integral_swap (hwint t 0)]
      exact (integral_sub ((hwint 0 t).integral_prod_right) ((hwint t 0).integral_prod_right)).symm
    calc
      ⟪z, U t - U 0⟫_ℂ = ∫ x, ⟪z x, u t x - u 0 x⟫_ℂ ∂m := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (U t) (U 0), hU t, hU 0] with x hx ht h0
        rw [hx, Pi.sub_apply, ht, h0]
      _ = ∫ x, (∫ s in (0 : ℝ)..t, w s x) ∂m :=
        integral_congr_ae (ae_of_all _ fun x => (hpoint x).symm)
      _ = ∫ s in (0 : ℝ)..t, ⟪z, V s⟫_ℂ := by
        rw [← hswap]
        apply intervalIntegral.integral_congr
        intro s _
        change (∫ x, w s x ∂m) = ⟪z, V s⟫_ℂ
        rw [L2.inner_def]
        exact integral_congr_ae ((hV s).mono fun x hx => congrArg (inner ℂ (z x)) hx.symm)
      _ = ⟪z, (∫ s in (0 : ℝ)..t, V s)⟫_ℂ :=
        (innerSL ℂ z).intervalIntegral_comp_comm (hVc.intervalIntegrable 0 t)
  have heq : U = fun t => (∫ s in (0 : ℝ)..t, V s) + U 0 :=
    funext fun t => sub_eq_iff_eq_add.mp (hFTC t)
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hVc.intervalIntegrable 0 0)
    (hVc.stronglyMeasurableAtFilter volume _) hVc.continuousAt).add_const _

end Analysis

open Langlands.GroupScheme

local instance derivativeGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance derivativeGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "GLr" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "EH" => GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)
local notation "ev" => Langlands.Automorphic.ContinuousRationalFunctions.evaluate F (r + 1)

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "Γ" => positiveRationalSubgroup F GLr T i
local notation "Qp" => PositiveRationalQuotient F GLr T i
local notation "mQ" => positiveRationalQuotientHaarMeasure F GLr T i
local notation "hR" => haarQuotientMeasureRightInvariant F GLr T i hi I e hc
local notation "ρ" => quotientL2RightTranslate F GLr T i mQ hR

/-- The real archimedean exponential curve as a curve of group-scheme adelic points. -/
abbrev exponentialAdelicPoint (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (t : ℝ) :
    AdelicGroupPoints F GLr :=
  (EH).symm (AdelicGL.ofInfinite F (r + 1) (ArchimedeanGL.realLieExponentialCurve F (r + 1) X t))

local notation "aX" => exponentialAdelicPoint F r
local notation "D" => fun X => finiteSmoothEnvelopingAction F (r + 1)
  (ArchimedeanGL.envelopingGenerator F (r + 1) (ArchimedeanGL.complexify F (r + 1) X))

omit [(characterRestrict i).range.FiniteIndex]
  [(Measure.haar : Measure (normOneSubgroup F GLr)).IsMulRightInvariant] in
private theorem eval_pullback (h : C(Qp, ℂ)) (g : AdelicGroupPoints F GLr) :
    ev (continuousGeneralLinearEquiv F (r + 1) (positiveQuotientContinuousPullback F GLr T i h))
        (EH g) = h (LeftCosetSpace.mk Γ g) := by
  exact congrArg (fun g' : AdelicGroupPoints F GLr => h (LeftCosetSpace.mk Γ g'))
    ((EH).symm_apply_apply g)

omit [(characterRestrict i).range.FiniteIndex]
  [(Measure.haar : Measure (normOneSubgroup F GLr)).IsMulRightInvariant] in
private theorem eval_translate (X : ArchimedeanGL.RealLieAlgebra F (r + 1))
    (b : C(Qp, ℂ)) (f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1))
    (hb : continuousGeneralLinearEquiv F (r + 1) (positiveQuotientContinuousPullback F GLr T i b) = f)
    (g : AdelicGroupPoints F GLr) (s : ℝ) :
    b (LeftCosetSpace.rightTranslate Γ (aX X s) (LeftCosetSpace.mk Γ g)) =
      ev f (EH g * AdelicGL.ofInfinite F (r + 1) (ArchimedeanGL.realLieExponentialCurve F (r + 1) X s)) := by
  let y := g * aX X s
  have hy : EH y = EH g * AdelicGL.ofInfinite F (r + 1)
      (ArchimedeanGL.realLieExponentialCurve F (r + 1) X s) :=
    ((EH).map_mul g (aX X s)).trans (congrArg (EH g * ·) ((EH).apply_symm_apply _))
  exact (eval_pullback F r T i b y).symm.trans <|
    (congrArg (fun b' => ev b' (EH y)) hb).trans (congrArg (ev f) hy)

omit [(characterRestrict i).range.FiniteIndex]
  [(Measure.haar : Measure (normOneSubgroup F GLr)).IsMulRightInvariant] in
private theorem pointwise_quotient_hasDerivAt (X : ArchimedeanGL.RealLieAlgebra F (r + 1))
    (h k : C(Qp, ℂ)) (f : FiniteSmoothRationalFunctions F (r + 1))
    (hf : continuousGeneralLinearEquiv F (r + 1) (positiveQuotientContinuousPullback F GLr T i h) = f.val)
    (hk : continuousGeneralLinearEquiv F (r + 1) (positiveQuotientContinuousPullback F GLr T i k) =
      ((D) X f).val) (t : ℝ) (q : Qp) :
    HasDerivAt (fun s => h (LeftCosetSpace.rightTranslate Γ (aX X s) q))
      (k (LeftCosetSpace.rightTranslate Γ (aX X t) q)) t := by
  obtain ⟨g, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  have hv := eval_translate F r T i X k ((D) X f).val hk g t
  have hu := funext (eval_translate F r T i X h f.val hf g)
  rw [hu, hv]
  exact evaluate_exponential_hasDerivAt F (r + 1) X f (EH g) t

set_option maxHeartbeats 400000 in
/-- The same differentiation comparison in ambient quotient `L²`, for any finite-smooth
rational function and its true real differential, once the two form classes are supplied. -/
theorem quotient_hasDerivAt_of_formClasses
    (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (f : FiniteSmoothRationalFunctions F (r + 1))
    (φ ψ : Lp ℂ 2 mQ)
    (hφ : IsGeneralLinearFormClass F r T i φ f.val)
    (hψ : IsGeneralLinearFormClass F r T i ψ ((D) X f).val) :
    HasDerivAt (fun t : ℝ => ρ (aX X t) φ) ψ 0 := by
  let := positiveRationalQuotient_borelSpace F GLr T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F GLr T i hi I e hc
  obtain ⟨h, hf, hφh⟩ := hφ
  obtain ⟨k, hk, hψk⟩ := hψ
  have ha : Continuous (aX X) := (EH).symm.continuous.comp <|
    (AdelicGL.ofInfinite F (r + 1)).continuous.comp (continuous_exponentialCurve F (r + 1) X)
  have ha0 : aX X 0 = 1 := by simp only [exponentialAdelicPoint,
    ArchimedeanGL.realLieExponentialCurve_zero, map_one]
  let translate (t : ℝ) (q : Qp) := LeftCosetSpace.rightTranslate Γ (aX X t) q
  have htrans : Continuous (Function.uncurry translate) :=
    continuous_smul.comp (((MulOpposite.continuous_op.comp ha).comp continuous_fst).prodMk
      continuous_snd)
  have hcoe (z : Lp ℂ 2 mQ) (b : C(Qp, ℂ)) (hz : (z : Qp → ℂ) =ᵐ[mQ] b) (t : ℝ) :
      ((ρ (aX X t) z : Lp ℂ 2 mQ) : Qp → ℂ) =ᵐ[mQ] fun q => b (translate t q) :=
    (coeFn_quotientL2RightTranslate F GLr T i mQ hR (aX X t) z).trans
      ((hR (aX X t)).quasiMeasurePreserving.ae_eq_comp hz)
  have hcψ : Continuous (fun t : ℝ => ρ (aX X t) ψ) :=
    (haarQuotientL2OrbitMap F GLr T i hi I e hc ψ).continuous.comp ha
  let v (t : ℝ) (q : Qp) := k (translate t q)
  have hv : Continuous (Function.uncurry v) := k.continuous.comp htrans
  have hψ0 : ρ (aX X 0) ψ = ψ :=
    (congrArg (fun a : AdelicGroupPoints F GLr => ρ a ψ) ha0).trans
      (quotientL2RightTranslate_one F GLr T i mQ hR ψ)
  let U : ℝ → Lp ℂ 2 mQ := fun t => ρ (aX X t) φ
  let V : ℝ → Lp ℂ 2 mQ := fun t => ρ (aX X t) ψ
  let u : ℝ → Qp → ℂ := fun t q => h (translate t q)
  have hV (t : ℝ) : ‖V t‖ ≤ ‖ψ‖ := le_of_eq <| LinearIsometry.norm_map (ρ (aX X t)) ψ
  have hvc (q : Qp) : Continuous (fun t => v t q) := uncurry_continuous_section (v := v) hv q
  have hm : Measurable (Function.uncurry v) := Continuous.measurable hv
  have hsf : SigmaFinite mQ := inferInstance
  have hpoint := pointwise_quotient_hasDerivAt F r T i X h k f hf hk
  have hd : HasDerivAt U (V 0) 0 :=
    @hasDerivAt_L2_of_pointwise Qp _ mQ hsf U V u v ‖ψ‖
      (hcoe φ h hφh) (hcoe ψ k hψk) hm hvc hcψ hV hpoint
  exact Eq.mp (congrArg (fun y : Lp ℂ 2 mQ => HasDerivAt U y 0) hψ0) hd

end Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearFormClassDerivative

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open GeneralLinearFormClassDerivative

set_option maxHeartbeats 1000000 in
/-- The genuine real Lie action on a cusp form differentiates the right orbit of its `L²` class. -/
theorem generalLinearCuspidalFormClassDerivative :
    GeneralLinearCuspidalFormClassDerivativeStatement.{u} := by
  intro F _ _ _ r hPD T i hi _ I _ e hc _ hG S πc R X f φ ψ hφ hψ
  have h := quotient_hasDerivAt_of_formClasses F r T i hi I e hc X f.val.val
    (φ : Lp ℂ 2 _) (ψ : Lp ℂ 2 _) hφ hψ
  rw [hasDerivAt_iff_tendsto_slope_zero] at h ⊢
  rw [tendsto_subtype_rng]
  exact h

end Langlands.Automorphic.GroupSchemeFunctions
