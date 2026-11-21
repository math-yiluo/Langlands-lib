import Langlands.Global.RankinSelberg.RealUnequalOrdinaryFamily

/-! # Joint holomorphy of the real dual unequal-rank integral over a parameter family -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalFamily

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open Langlands.QuotientIntegration (descend leftQuotient_isOpenQuotientMap)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
  RealRectangularIwasawa
open RealUnequalDualConvergence (rectDecay integrable_rectDecay sigmaFinite_rect
  exp_neg_mul_log_le sum_coord_le integrable_exp_comp_alphaQ continuous_rectangularPoint)
open ComplexUnequalFamily (HalfPlaneDomination differentiableOn_integral_of_halfPlaneDomination)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

/-! ### Left characters of the dual functions -/

/-- The Weyl inverse transpose of a function with the left character of `b` has the left
character of `-b`. -/
theorem HasLeftCharacter.dual {n : ℕ} {b : ℝˣ} {V : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hV : HasLeftCharacter b V) : HasLeftCharacter (-b) (ArchimedeanLocal.dualFunction (n + 1) V) := by
  intro u hu g
  show V (GeneralLinear.weylInverseTranspose (n + 1) ℝ (u * g)) =
    realWhittakerCharacter (-b) u * V (GeneralLinear.weylInverseTranspose (n + 1) ℝ g)
  rw [show u * g = (⟨u, hu⟩ : Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ).val * g
      from rfl, Langlands.Whittaker.weylInverseTranspose_left_unipotent,
    hV _ (Langlands.Whittaker.reflectedUnipotent ⟨u, hu⟩).2,
    RealUnequalPairConvergence.realWhittakerCharacter_reflected]

variable {r t : ℕ} (h : t < r) {a : ℝˣ}
local notation "GT" => Langlands.GeneralLinear (t + 1) ℝ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Rect" => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ

/-- The translated Weyl inverse transpose `g ↦ W̃(g w_(n,m))` of a function with the left
character of `a` has the left character of `-a`. -/
theorem HasLeftCharacter.dualTranslate {W : GR → ℂ} (hW : HasLeftCharacter a W) :
    HasLeftCharacter (-a) (ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W)) := by
  intro u hu g
  show W (GeneralLinear.weylInverseTranspose (r + 1) ℝ (u * g * ArchimedeanLocal.unfoldingWeyl h)) =
    realWhittakerCharacter (-a) u *
      W (GeneralLinear.weylInverseTranspose (r + 1) ℝ (g * ArchimedeanLocal.unfoldingWeyl h))
  rw [mul_assoc, show u * (g * ArchimedeanLocal.unfoldingWeyl h) =
      (⟨u, hu⟩ : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ).val * (g * ArchimedeanLocal.unfoldingWeyl h)
        from rfl, Langlands.Whittaker.weylInverseTranspose_left_unipotent,
    hW _ (Langlands.Whittaker.reflectedUnipotent ⟨u, hu⟩).2,
    RealUnequalPairConvergence.realWhittakerCharacter_reflected]

/-- The product of the two dual functions in the dual kernel is left invariant in the group
variable under the upper unipotent group of the smaller group. -/
theorem dualProduct_unipotent_mul {W : GR → ℂ} {V : GT → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) (g : GT) (x : Rect) :
    ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.rectangularPoint h (u.val * g) x) * ArchimedeanLocal.dualFunction (t + 1) V (u.val * g) =
      ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W) (ArchimedeanLocal.rectangularPoint h g x) *
        ArchimedeanLocal.dualFunction (t + 1) V g := by
  have hVd := hW.dualTranslate h
  have hV'd : HasLeftCharacter a (ArchimedeanLocal.dualFunction (t + 1) V) := by
    have h' := hV.dual
    rwa [neg_neg] at h'
  rw [RealUnequalPairConvergence.rectangularPoint_mul,
    RealUnequalPairConvergence.rectangularPoint_zero,
    hVd _ (RealUnequalConvergence.padGL_mem_upperUnipotent _ u.2),
    RealUnequalConvergence.realWhittakerCharacter_padGL h, hV'd u.val u.2 g]
  calc
    _ = (realWhittakerCharacter (-a) u.val * realWhittakerCharacter (-(-a)) u.val) *
        (ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W)
          (ArchimedeanLocal.rectangularPoint h g x) * ArchimedeanLocal.dualFunction (t + 1) V g) := by
      rw [neg_neg]
      ring
    _ = _ := by rw [realWhittakerCharacter_mul_neg, one_mul]

/-- The real dual kernel evaluated at the class of any representative. -/
theorem dualKernel_mk {W : GR → ℂ} {V : GT → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (s : ℂ) (g : GT) (x : Rect) :
    realUnequalDualKernel h W V s (Quotient.mk _ g, x) =
      ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W) (ArchimedeanLocal.rectangularPoint h g x) *
        ArchimedeanLocal.dualFunction (t + 1) V g *
        Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (logDet g : ℂ)) := by
  let f : GT → ℂ := fun g =>
    ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W) (ArchimedeanLocal.rectangularPoint h g x) *
      ArchimedeanLocal.dualFunction (t + 1) V g * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (logDet g : ℂ))
  have hf : ∀ u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g, f (u.val * g) = f g := by
    intro u g
    simp only [f]
    rw [dualProduct_unipotent_mul h hW hV, logDet_unipotent_mul]
  exact congrArg (descend _ f hf) (Quotient.out_eq (Quotient.mk _ g))

/-- The real dual kernel is continuous on the product of the quotient and the rectangular
matrix space. -/
theorem continuous_dualKernel {W : GR → ℂ} {V : GT → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (s : ℂ) :
    Continuous (realUnequalDualKernel h W V s) := by
  have hq := (leftQuotient_isOpenQuotientMap
    (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ)).prodMap (IsOpenQuotientMap.id (X := Rect))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : GT × Rect => realUnequalDualKernel h W V s (Quotient.mk _ p.1, p.2))
  simp only [dualKernel_mk h hW hV]
  have hVdc : Continuous (ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W)) :=
    (RealEqualDualConvergence.continuous_dual hWc).comp (continuous_id.mul continuous_const)
  exact ((hVdc.comp (continuous_rectangularPoint h)).mul
    ((RealEqualDualConvergence.continuous_dual hVc).comp continuous_fst)).mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_logDet.comp continuous_fst))))

/-- Uniform gauge estimates give common integrable product majorants for the real dual kernel on
bounded intervals of the real part of the spectral variable above a fixed threshold, for any
self-dual normalization of the rectangular measure. -/
theorem dual_halfPlaneDomination {P : Type*} (D : RealQuotientMeasureData t) (b : ℝˣ)
    (S : Set P) (W : P → GR → ℂ) (V : P → GT → ℂ) (s : P → ℂ)
    (hW : ∀ p, HasLeftCharacter a (W p)) (hV : ∀ p, HasLeftCharacter (-a) (V p))
    (hWb : HasUniformGauge S W) (hVb : HasUniformGauge S V) :
    ∃ σ, HalfPlaneDomination (realUnequalDualMeasure (r := r) b D) S s
      (fun p => realUnequalDualKernel h (W p) (V p) (s p)) σ := by
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, L, hκL⟩ :=
    exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  have hρσ : SigmaFinite (rectangularMeasure (realSelfDualMeasure b) (r - (t + 1)) (t + 1)) :=
    sigmaFinite_rect _ _ _
  obtain ⟨N1, hN1⟩ := (hWb.dual.translate
    (RealUnequalPairConvergence.unfoldingWeyl_mem_unitary h)).rect h
    (fun p _ => ((hW p).dualTranslate h).norm_eq)
  obtain ⟨N2, hN2⟩ := hVb.dual
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  set A : ℝ := (N1 : ℝ) + N2 + ‖L‖ with hA
  set c : ℝ := ((r - t : ℕ) : ℝ) / 2 with hc
  have hA0 : 0 ≤ A := by positivity
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hd0 : (0 : ℝ) ≤ ((r - (t + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN10 : (0 : ℝ) ≤ N1 := Nat.cast_nonneg N1
  have hextra : 0 ≤ 2 * (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) +
      2 * ((t : ℝ) + 1) * ((r - (t + 1) : ℕ) : ℝ) := by positivity
  refine ⟨A + 1 + c, fun τ => ?_⟩
  set M : ℕ := ⌈A + (τ - c) + 1 + 2 * (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) +
    2 * ((t : ℝ) + 1) * ((r - (t + 1) : ℕ) : ℝ)⌉₊ with hM
  have hMle := Nat.le_ceil (A + (τ - c) + 1 + 2 * (N1 : ℝ) *
    (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) + 2 * ((t : ℝ) + 1) * ((r - (t + 1) : ℕ) : ℝ))
  rw [← hM] at hMle
  have hMt : 0 ≤ (M : ℝ) * t := by positivity
  obtain ⟨C1, hC1, hb1⟩ := hN1 M
  refine ⟨fun z => C1 * C2 * Real.exp (-(∑ j, |alphaQ z.1 j|) - L (alphaQ z.1)) * rectDecay z.2,
    ((integrable_exp_comp_alphaQ hκL (continuous_exp_neg_sum_abs_sub L)
      (fun y => by linarith)).const_mul (C1 * C2)).mul_prod (integrable_rectDecay _ _ _),
    fun v hv hvσ hvτ z => ?_⟩
  set T : ℝ := (s v).re - c with hT
  have hT1 : A + 1 ≤ T := by linarith
  have hTτ : T ≤ τ - c := by linarith
  have hre : (s v - ((r - t : ℕ) : ℂ) / 2).re = T := by
    rw [hT, hc, Complex.sub_re, Complex.div_re]
    simp
    ring
  have hrep : ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)) (x : Rect),
      ‖realUnequalDualKernel h (W v) (V v) (s v) (Quotient.mk _ (torus y * (k : GT)), x)‖ ≤
        C1 * C2 * Real.exp (-(∑ j, |y j|) - L y) * rectDecay x := by
    intro y k x
    rw [dualKernel_mk h (hW v) (hV v), norm_mul, norm_mul, logDet_torus_mul,
      norm_cexp_mul_ofReal, hre]
    have h1 := hb1 v hv y k x
    have h2 := hb2 v hv y k
    have hκ : (((t + 1 : ℕ) : ℝ)) * ((r - (t + 1) : ℕ) : ℝ) ≤
        (M : ℝ) * ((t : ℝ) + 1) / 2 -
          (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) := by
      push_cast
      linarith
    have hx := exp_neg_mul_log_le x hκ
    have hcoord := sum_coord_le y hA0 hT1 (M := (M : ℝ)) (by linarith)
    have hLy := linear_le L y
    set Λ := Real.log (1 + frob x) with hΛ
    have hexp : Real.exp (-(M : ℝ) * (∑ j, max (y j) 0 + ((t : ℝ) + 1) * Λ / 2) +
          (N1 : ℝ) * (∑ j, |y j| + (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Λ)) *
        Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|) *
        Real.exp (T * ∑ j, y j) =
        Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + ((N1 : ℝ) + N2) * ∑ j, |y j| +
          T * ∑ j, y j) *
        Real.exp (-((M : ℝ) * ((t : ℝ) + 1) / 2 -
          (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ))) * Λ) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have h3 : Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + ((N1 : ℝ) + N2) * ∑ j, |y j| +
        T * ∑ j, y j) ≤ Real.exp (-(∑ j, |y j|) - L y) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hA] at hcoord
      linarith
    calc
      _ ≤ (C1 * Real.exp (-(M : ℝ) * (∑ j, max (y j) 0 + ((t : ℝ) + 1) * Λ / 2) +
            (N1 : ℝ) * (∑ j, |y j| + (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Λ))) *
          (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
          Real.exp (T * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (Real.exp_nonneg _)
      _ = C1 * C2 * (Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + ((N1 : ℝ) + N2) * ∑ j, |y j| +
            T * ∑ j, y j) *
          Real.exp (-((M : ℝ) * ((t : ℝ) + 1) / 2 -
            (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ))) * Λ)) := by
        rw [← hexp]
        ring
      _ ≤ C1 * C2 * (Real.exp (-(∑ j, |y j|) - L y) * rectDecay x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h3 hx (Real.exp_nonneg _) (Real.exp_nonneg _))
          (mul_nonneg hC1 hC2)
      _ = _ := by ring
  obtain ⟨q, x⟩ := z
  induction q using Quotient.inductionOn with
  | h g =>
    dsimp only
    rw [alphaQ_mk, mk_eq_mk_torus_mul_kpart g]
    exact hrep (alpha g) (kpart g) x

local instance dualFamilyMatrixSecondCountable : SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin (t + 1) → Fin (t + 1) → ℝ))
local instance dualFamilyGLSecondCountable : SecondCountableTopology GT :=
  (Units.isOpenEmbedding_val (R := Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ)).isInducing.secondCountableTopology
local instance dualFamilyMatrixLocallyCompact :
    LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℝ))
local instance dualFamilyQuotientSigmaCompact : SigmaCompactSpace (LeftUnipotentQuotient t ℝ) := by
  have hq := leftQuotient_isOpenQuotientMap (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ)
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

/-- On absolute convergence, the iterated real dual integral is the product integral. -/
theorem dualIntegral_eq_prod (D : RealQuotientMeasureData t) (b : ℝˣ)
    (W : GR → ℂ) (V : GT → ℂ) (s : ℂ)
    (hint : Integrable (realUnequalDualKernel h W V s) (realUnequalDualMeasure (r := r) b D)) :
    realUnequalDualIntegral h b D W V s =
      ∫ z, realUnequalDualKernel h W V s z ∂realUnequalDualMeasure (r := r) b D := by
  have : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  have : D.measure.Regular := D.compatible.regular
  have : SigmaFinite (rectangularMeasure (realSelfDualMeasure b) (r - (t + 1)) (t + 1)) :=
    sigmaFinite_rect _ _ _
  exact (integral_prod _ hint).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Holomorphy and integrability of the real dual unequal-rank integral, jointly in a
finite-dimensional complex parameter space, for families with uniform gauge estimates and for
any self-dual normalization `b` of the rectangular measure. -/
def RealUnequalDualFamilyStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (b : ℝˣ) (S : Set E) (W : E → GR → ℂ) (V : E → GT → ℂ)
    (s : E → ℂ), IsOpen S → Differentiable ℂ s →
    (∀ p, HasLeftCharacter a (W p)) → (∀ p, HasLeftCharacter (-a) (V p)) →
    (∀ p, Continuous (W p)) → (∀ p, Continuous (V p)) →
    (∀ g, DifferentiableOn ℂ (W · g) S) → (∀ g, DifferentiableOn ℂ (V · g) S) →
    HasUniformGauge S W → HasUniformGauge S V →
    ∃ σ : ℝ,
      (∀ p ∈ S ∩ {v | σ < (s v).re}, Integrable (realUnequalDualKernel h (W p) (V p) (s p))
        (realUnequalDualMeasure (r := r) b D)) ∧
      DifferentiableOn ℂ (fun p => realUnequalDualIntegral h b D (W p) (V p) (s p))
        (S ∩ {v | σ < (s v).re})

theorem realUnequalDualFamily : RealUnequalDualFamilyStatement (E := E) (a := a) h := by
  intro D b S W V s hS hs hW hV hWc hVc hWd hVd hWb hVb
  obtain ⟨σ, hdom⟩ := dual_halfPlaneDomination h D b S W V s hW hV hWb hVb
  have hD (z : LeftUnipotentQuotient t ℝ × Rect) :
      DifferentiableOn ℂ (fun p => realUnequalDualKernel h (W p) (V p) (s p) z) S := by
    let g := z.1.out
    let g₁ := GeneralLinear.weylInverseTranspose (r + 1) ℝ
      (ArchimedeanLocal.rectangularPoint h g z.2 * ArchimedeanLocal.unfoldingWeyl h)
    let g₂ := GeneralLinear.weylInverseTranspose (t + 1) ℝ g
    change DifferentiableOn ℂ (fun p => W p g₁ * V p g₂ *
      Complex.exp ((s p - ((r - t : ℕ) : ℂ) / 2) * (logDet g : ℂ))) S
    exact ((hWd _).mul (hVd _)).mul
      (Complex.differentiable_exp.comp ((hs.sub_const _).mul_const _)).differentiableOn
  obtain ⟨hint, hdiff⟩ := differentiableOn_integral_of_halfPlaneDomination hS hs (fun p =>
    (continuous_dualKernel h (hW p) (hV p) (hWc p) (hVc p) (s p)).aestronglyMeasurable) hD hdom
  exact ⟨σ, hint, hdiff.congr fun p hp => dualIntegral_eq_prod h D b (W p) (V p) (s p) (hint p hp)⟩

end Langlands.Global.RankinSelbergGlobal.RealUnequalFamily
