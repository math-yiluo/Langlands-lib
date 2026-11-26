import Langlands.Global.RankinSelberg.RealMatrixScaledFunctionalEquation
import Langlands.Global.RankinSelberg.RealPositionDeterminantTwist

/-! # The real square matrix functional equation for determinant-twisted coefficients -/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Matrix Matrix.Norms.Operator SchwartzMap Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.Archimedean.RealJacquetFrobenius (charFun charData charData_character_apply)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanDeterminantTheta RealSquareFourier RealPrincipalSeries

local instance realTwistMatrixGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realTwistMatrixGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ
local notation "dp" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "absC" => fun b : ℝˣ => ((|(b : ℝ)| : ℝ) : ℂ)

/-! ### Shifting the complex parameter -/

private theorem eventually_codiscrete_comp_add {p : ℂ → Prop} (w : ℂ)
    (h : ∀ᶠ t in codiscrete ℂ, p t) : ∀ᶠ s in codiscrete ℂ, p (s + w) := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE] at h ⊢
  intro x
  have ht : Tendsto (fun s : ℂ => s + w) (𝓝[≠] x) (𝓝[≠] (x + w)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_id.add continuous_const).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_compl_iff, mem_singleton_iff, add_left_inj] at hs ⊢
      exact hs
  exact ht.eventually (h (x + w))

private theorem meromorphicOn_comp_add {M : ℂ → ℂ} (hM : MeromorphicOn M univ) (w : ℂ) :
    MeromorphicOn (fun s => M (s + w)) univ := fun z _ =>
  (hM (z + w) (mem_univ _)).comp_analyticAt (g := fun s : ℂ => s + w)
    (analyticAt_id.add analyticAt_const)

theorem realMatrixZetaKernel_shift {F F' : G → ℂ} (Φ : Mat → ℂ) (w : ℂ)
    (hF : ∀ g, F' g = dp g w * F g) (s : ℂ) :
    realMatrixZetaKernel F' Φ s = realMatrixZetaKernel F Φ (s + w) := by
  funext g
  have hx : ((|g.val.det| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)).ne'
  change Φ g.val * F' g * dp g (s + (r : ℂ) / 2) = Φ g.val * F g * dp g (s + w + (r : ℂ) / 2)
  rw [hF, realDetPower_eq_cpow, realDetPower_eq_cpow, realDetPower_eq_cpow,
    show s + w + (r : ℂ) / 2 = w + (s + (r : ℂ) / 2) by ring, Complex.cpow_add w (s + (r : ℂ) / 2) hx]
  ring

/-- Multiplying a coefficient by `|det|^w` translates its zeta integral by `w`. -/
theorem realMatrixZeta_shift (μ : Measure G) {F F' : G → ℂ} (Φ : Mat → ℂ) (w : ℂ)
    (hF : ∀ g, F' g = dp g w * F g) (s : ℂ) :
    realMatrixZeta μ F' Φ s = realMatrixZeta μ F Φ (s + w) := by
  unfold realMatrixZeta
  rw [realMatrixZetaKernel_shift Φ w hF]

/-- Multiplying the primal coefficient by `|det|^w` and the dual one by `|det|^(-w)` translates
the established equation by `w`. -/
theorem realMatrixEquation_shift (μ : Measure G) {F Fd F' Fd' : G → ℂ} (Φ Φd : Mat → ℂ) (w : ℂ)
    (hF : ∀ g, F' g = dp g w * F g) (hFd : ∀ g, Fd' g = dp g (-w) * Fd g)
    {L Ld E : ℂ → ℂ} (h : HasRealMatrixEquation μ F Φ Fd Φd L Ld E) :
    HasRealMatrixEquation μ F' Φ Fd' Φd (fun s => L (s + w)) (fun t => Ld (t - w))
      (fun s => E (s + w)) := by
  have hk (s : ℂ) := realMatrixZetaKernel_shift Φ w hF s
  have hkd (s : ℂ) : realMatrixZetaKernel Fd' Φd s = realMatrixZetaKernel Fd Φd (s + -w) :=
    realMatrixZetaKernel_shift Φd (-w) hFd s
  have hZ : realMatrixZeta μ F' Φ = fun s => realMatrixZeta μ F Φ (s + w) := by
    funext s
    unfold realMatrixZeta
    rw [hk]
  have hZd : realMatrixZeta μ Fd' Φd = fun s => realMatrixZeta μ Fd Φd (s + -w) := by
    funext s
    unfold realMatrixZeta
    rw [hkd]
  obtain ⟨σ, M, Md, hInt, hHol, hHold, hM, hMd, hEq, hEqd, hFE⟩ := h
  have h1 (s : ℂ) (hs : σ + |w.re| < s.re) : σ < (s + w).re := by
    rw [Complex.add_re]
    linarith [neg_abs_le w.re]
  have h2 (s : ℂ) (hs : σ + |w.re| < s.re) : σ < (s + -w).re := by
    rw [Complex.add_re, Complex.neg_re]
    linarith [le_abs_self w.re]
  refine ⟨σ + |w.re|, fun s => M (s + w), fun s => Md (s + -w), fun s hs => ?_, ?_, ?_,
    meromorphicOn_comp_add hM w, meromorphicOn_comp_add hMd (-w), fun s hs => ?_, fun s hs => ?_, ?_⟩
  · rw [hk, hkd]
    exact ⟨(hInt _ (h1 s hs)).1, (hInt _ (h2 s hs)).2⟩
  · rw [hZ]
    exact hHol.comp (differentiable_id.add_const w).differentiableOn fun s hs => h1 s hs
  · rw [hZd]
    exact hHold.comp (differentiable_id.add_const (-w)).differentiableOn fun s hs => h2 s hs
  · rw [hZ]
    exact hEq _ (h1 s hs)
  · rw [hZd]
    exact hEqd _ (h2 s hs)
  · filter_upwards [eventually_codiscrete_comp_add w hFE] with s hs
    rw [show 1 - s + -w = 1 - (s + w) by ring, show 1 - s - w = 1 - (s + w) by ring]
    exact hs

/-! ### Sign twists -/

private theorem det_matrixExpUnit_pos (X : Mat) (t : ℝ) : 0 < (matrixExpUnit n (t • X)).val.det := by
  have h := matrixExpUnit_add_smul n X (t / 2) (t / 2)
  rw [add_halves] at h
  rw [h, Units.val_mul, Matrix.det_mul]
  exact mul_self_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)

private theorem signCharacter_exp (p : Fin 2) (X : Mat) (t : ℝ) :
    realDetCharacter (charData p 0) (matrixExpUnit n (t • X)) = 1 := by
  rw [realDetCharacter_apply]
  have hp := det_matrixExpUnit_pos X t
  change charFun p 0 _ = 1
  rw [Langlands.Archimedean.RealJacquetFrobenius.charFun, abs_of_pos hp, div_self hp.ne', Complex.ofReal_one, one_pow, Complex.cpow_zero, one_mul]

/-- A sign of the determinant has vanishing right derivatives. -/
theorem rightDerivative_signCharacter (p : Fin 2) (X : Mat) (g : G) :
    rightDerivative (matrixModel ℝ n) X (realDetCharacter (charData p 0)) g = 0 := by
  have h := hasDerivAt_mul_matrixExpUnit_smul
    ((@contMDiff_realDetCharacter (r + 1) (charData p 0)).of_le (by norm_num)) g X
  have hc : (fun s : ℝ => realDetCharacter (charData p 0) (g * matrixExpUnit n (s • X))) =
      fun _ => realDetCharacter (charData p 0) g := by
    funext s
    rw [realDetCharacter_mul, signCharacter_exp, mul_one]
  rw [hc] at h
  exact h.unique (hasDerivAt_const _ _)

theorem iteratedRightDerivative_signCharacter_mul (p : Fin 2) {h : G → ℂ}
    (hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ h) (Xs : List Mat) :
    RealLocalWhittaker.iteratedRightDerivative r Xs
        (fun g => realDetCharacter (charData p 0) g * h g) =
      fun g => realDetCharacter (charData p 0) g * RealLocalWhittaker.iteratedRightDerivative r Xs h g := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change rightDerivative (matrixModel ℝ n) X
      (RealLocalWhittaker.iteratedRightDerivative r Xs _) = _
    rw [ih]
    funext g
    rw [RealPrincipalSeriesDuality.rightDerivative_mul_fun (contMDiff_realDetCharacter _)
      (RealUniformWhittaker.contMDiff_iteratedRightDerivative hh Xs), rightDerivative_signCharacter,
      zero_mul, zero_add]
    rfl

theorem signCharacter_sq (p : Fin 2) (x : ℝˣ) :
    ((charData p 0).character x : ℂ) * ((charData p 0).character x : ℂ) = 1 := by
  rw [charData_character_apply, Langlands.Archimedean.RealJacquetFrobenius.charFun, Complex.cpow_zero, mul_one]
  exact Langlands.LocalFactor.RealTate.sign_pow_mul_self x.ne_zero p

private theorem norm_signCharacter (p : Fin 2) (g : G) :
    ‖realDetCharacter (charData p 0) g‖ = 1 := by
  rw [norm_realDetCharacter]
  change |g.val.det| ^ (0 : ℂ).re = 1
  rw [Complex.zero_re, Real.rpow_zero]

/-- Multiplication by a determinant character between principal series. -/
def detCharacterMul (c : RealCharacterData) {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ : ∀ (i : Fin n) (x : ℝˣ), χ' i x = χ i x * (c.character x : ℂ)) :
    principalSeries ℝ n χ →ₗ[ℂ] principalSeries ℝ n χ' where
  toFun f := ⟨fun g => realDetCharacter c g * (f : G → ℂ) g,
    realDetCharacter_mul_mem_principalSeries c hχ f.2⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    exact mul_add _ _ _
  map_smul' z f := by
    apply Subtype.ext
    funext g
    exact mul_left_comm _ _ _

theorem signTwist_back (ds : List RealBlock) (p : Fin 2) (i : I) (x : ℝˣ) :
    realPositionCharacter ds i x =
      realPositionCharacter (twistedPositionList n ds (charData p 0)) i x *
        ((charData p 0).character x : ℂ) := by
  rw [realPositionCharacter_twistedPositionList, mul_assoc, signCharacter_sq, mul_one]

/-- A sign twist preserves compact derivative bounds for linear forms. -/
theorem hasCompactDerivativeBound_signTwist (ds : List RealBlock) (p : Fin 2)
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) :
    HasCompactDerivativeBound r (twistedPositionList n ds (charData p 0))
      (ℓ.comp (detCharacterMul (charData p 0) (signTwist_back ds p))) := by
  obtain ⟨m, Xs, A, hA, hb⟩ := hℓ
  refine ⟨m, Xs, A, hA, fun f B hB => hb _ B fun i k hk => ?_⟩
  change ‖RealLocalWhittaker.iteratedRightDerivative r (Xs i)
    (fun g => realDetCharacter (charData p 0) g * (f : G → ℂ) g) k‖ ≤ B i
  rw [iteratedRightDerivative_signCharacter_mul p f.2.1, norm_mul, norm_signCharacter, one_mul]
  exact hB i k hk

/-! ### The twisted equation -/

theorem realDetCharacter_eq_sign_mul (c : RealCharacterData) (g : G) :
    realDetCharacter c g = realDetCharacter (charData c.parity 0) g * dp g c.exponent := by
  rw [realDetCharacter_apply c, realDetCharacter_apply (charData c.parity 0), realDetPower_eq_cpow]
  change charFun c.parity c.exponent _ = charFun c.parity 0 _ * _
  simp only [Langlands.Archimedean.RealJacquetFrobenius.charFun, Complex.cpow_zero, mul_one]

theorem detPower_inverseTranspose (g : G) (w : ℂ) : dp (ιg g) w = dp g (-w) := by
  rw [realDetPower_eq_cpow, realDetPower_eq_cpow]
  change ((realNormalizedAbs (ιg g).val.det : ℝ) : ℂ) ^ w =
    ((realNormalizedAbs g.val.det : ℝ) : ℂ) ^ (-w)
  rw [realNormalizedAbs_det_inverseTranspose, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (show (0 : ℝ) ≤ realNormalizedAbs g.val.det from abs_nonneg _),
    Complex.cpow_neg]

/-- Real matrix continuation and reflection for the coefficient of a compact-derivative-bounded
form, multiplied by an arbitrary real character of the determinant. -/
def RealMatrixTwistedFunctionalEquationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r ds ℓ → ∀ (c : RealCharacterData) (Φ : 𝓢(Mat, ℂ)) (b : ℝˣ),
    let e (i : I) := RealBlockPosition.realPositionSign ds i + c.parity
    let u (i : I) := GramFormula.realPositionExponent ds i + c.exponent
    let F (g : G) := realDetCharacter c g * ℓ (translate r ds g f)
    let E (s : ℂ) := torusEpsilon e *
      (∏ i : I, realPositionCharacter ds i b * (c.character b : ℂ)) *
      absC b ^ (((n : ℕ) : ℂ) * (s - 1 / 2))
    HasRealMatrixEquation μ F Φ (F ∘ ιg) (matrixTransform b Φ) (torusL e u) (torusL e (-u)) E

/-- A determinant-character twist of a compact-derivative-bounded coefficient is the `|det|^w`
multiple of a compact-derivative-bounded coefficient of the sign-twisted position list. -/
theorem exists_signTwist_coefficient (ds : List RealBlock)
    (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (c : RealCharacterData) :
    ∃ (f' : principalSeries ℝ n
        (realPositionCharacter (twistedPositionList n ds (charData c.parity 0))))
      (ℓ' : principalSeries ℝ n
        (realPositionCharacter (twistedPositionList n ds (charData c.parity 0))) →ₗ[ℂ] ℂ),
      HasCompactDerivativeBound r (twistedPositionList n ds (charData c.parity 0)) ℓ' ∧
      ∀ g : G, realDetCharacter c g * ℓ (translate r ds g f) =
        dp g c.exponent * ℓ' (translate r (twistedPositionList n ds (charData c.parity 0)) g f') := by
  let c0 := charData c.parity 0
  let ds' := twistedPositionList n ds c0
  let M : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ]
      principalSeries ℝ n (realPositionCharacter ds') :=
    detCharacterMul (r := r) c0 (realPositionCharacter_twistedPositionList ds c0)
  let f' := M f
  let ℓ' := ℓ.comp (detCharacterMul (r := r) c0 (signTwist_back (r := r) ds c.parity))
  refine ⟨f', ℓ', hasCompactDerivativeBound_signTwist ds c.parity ℓ hℓ, fun g => ?_⟩
  have hcoef : ℓ' (translate r ds' g f') = realDetCharacter c0 g * ℓ (translate r ds g f) := by
    have hv : detCharacterMul (r := r) c0 (signTwist_back (r := r) ds c.parity) (translate r ds' g f') =
        realDetCharacter c0 g • translate r ds g f := by
      apply Subtype.ext
      funext x
      change realDetCharacter c0 x * (realDetCharacter c0 (x * g) * (f : G → ℂ) (x * g)) =
        realDetCharacter c0 g * (f : G → ℂ) (x * g)
      have hx : realDetCharacter c0 x * realDetCharacter c0 x = 1 :=
        signCharacter_sq c.parity (determinant x)
      rw [realDetCharacter_mul]
      linear_combination (realDetCharacter c0 g * (f : G → ℂ) (x * g)) * hx
    change ℓ (detCharacterMul (r := r) c0 (signTwist_back (r := r) ds c.parity) (translate r ds' g f')) = _
    rw [hv, map_smul, smul_eq_mul]
  change _ = dp g c.exponent * ℓ' (translate r ds' g f')
  rw [hcoef, realDetCharacter_eq_sign_mul]
  ring

/-- The torus `L`-product of the sign-twisted list, translated by the exponent of the
character, is the torus `L`-product of the twisted torus parameters. -/
theorem torusL_signTwist_shift (ds : List RealBlock) (c : RealCharacterData) (s : ℂ) :
    torusL (fun i : I =>
        RealBlockPosition.realPositionSign (twistedPositionList n ds (charData c.parity 0)) i)
      (fun i : I =>
        GramFormula.realPositionExponent (twistedPositionList n ds (charData c.parity 0)) i)
      (s + c.exponent) =
    torusL (fun i : I => RealBlockPosition.realPositionSign ds i + c.parity)
      (fun i : I => GramFormula.realPositionExponent ds i + c.exponent) s := by
  unfold torusL
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [realPositionSign_twistedPositionList, realPositionExponent_twistedPositionList]
  change Complex.Gammaℝ (s + c.exponent + (GramFormula.realPositionExponent ds i + 0) +
    ((RealBlockPosition.realPositionSign ds i + c.parity).val : ℂ)) = _
  congr 1
  ring

/-- The dual torus `L`-product of the sign-twisted list, translated by minus the exponent of
the character, is the dual torus `L`-product of the twisted torus parameters. -/
theorem torusL_neg_signTwist_shift (ds : List RealBlock) (c : RealCharacterData) (t : ℂ) :
    torusL (fun i : I =>
        RealBlockPosition.realPositionSign (twistedPositionList n ds (charData c.parity 0)) i)
      (-fun i : I =>
        GramFormula.realPositionExponent (twistedPositionList n ds (charData c.parity 0)) i)
      (t - c.exponent) =
    torusL (fun i : I => RealBlockPosition.realPositionSign ds i + c.parity)
      (-fun i : I => GramFormula.realPositionExponent ds i + c.exponent) t := by
  unfold torusL
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only [Pi.neg_apply]
  rw [realPositionSign_twistedPositionList, realPositionExponent_twistedPositionList]
  change Complex.Gammaℝ (t - c.exponent + -(GramFormula.realPositionExponent ds i + 0) +
    ((RealBlockPosition.realPositionSign ds i + c.parity).val : ℂ)) = _
  congr 1
  ring

theorem realMatrixTwistedFunctionalEquation :
    RealMatrixTwistedFunctionalEquationStatement (r := r) := by
  intro μ hμ κ hκ hκs ds f ℓ hℓ c Φ b e u F E
  let c0 := charData c.parity 0
  let ds' := twistedPositionList n ds c0
  obtain ⟨f', ℓ', hℓ', hcoef⟩ := exists_signTwist_coefficient ds f ℓ hℓ c
  let F0 (g : G) := ℓ' (translate r ds' g f')
  have h0 : HasRealMatrixEquation μ F0 Φ (F0 ∘ ιg) (matrixTransform b Φ)
      (torusL (fun i : I => RealBlockPosition.realPositionSign ds' i)
        (fun i : I => GramFormula.realPositionExponent ds' i))
      (torusL (fun i : I => RealBlockPosition.realPositionSign ds' i)
        (-fun i : I => GramFormula.realPositionExponent ds' i))
      (fun s => torusEpsilon (fun i : I => RealBlockPosition.realPositionSign ds' i) *
        (∏ i : I, realPositionCharacter ds' i b) * absC b ^ (((n : ℕ) : ℂ) * (s - 1 / 2))) :=
    realMatrixCompactFunctionalEquation (r := r) μ κ ds' f' ℓ' hℓ' Φ b
  have hF (g : G) : F g = dp g c.exponent * F0 g := hcoef g
  have hFd (g : G) : (F ∘ ιg) g = dp g (-c.exponent) * (F0 ∘ ιg) g := by
    change F (ιg g) = _ * F0 (ιg g)
    rw [hF, detPower_inverseTranspose]
  have key := realMatrixEquation_shift μ Φ (matrixTransform b Φ) c.exponent hF hFd h0
  have he0 (i : I) : RealBlockPosition.realPositionSign ds' i =
      RealBlockPosition.realPositionSign ds i + c.parity :=
    realPositionSign_twistedPositionList ds c0 i
  have hL : (fun s => torusL (fun i : I => RealBlockPosition.realPositionSign ds' i)
      (fun i : I => GramFormula.realPositionExponent ds' i) (s + c.exponent)) =
      torusL (fun i : I => RealBlockPosition.realPositionSign ds i + c.parity)
        (fun i : I => GramFormula.realPositionExponent ds i + c.exponent) :=
    funext (torusL_signTwist_shift ds c)
  have hLd : (fun t => torusL (fun i : I => RealBlockPosition.realPositionSign ds' i)
      (-fun i : I => GramFormula.realPositionExponent ds' i) (t - c.exponent)) =
      torusL (fun i : I => RealBlockPosition.realPositionSign ds i + c.parity)
        (-fun i : I => GramFormula.realPositionExponent ds i + c.exponent) :=
    funext (torusL_neg_signTwist_shift ds c)
  have hb : absC b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr b.ne_zero)
  have hcb : (c.character b : ℂ) = (c0.character b : ℂ) * absC b ^ c.exponent := by
    rw [c.character_eq, charData_character_apply, Langlands.Archimedean.RealJacquetFrobenius.charFun,
      Complex.cpow_zero, mul_one]
  have hprod : (∏ i : I, realPositionCharacter ds i b * (c.character b : ℂ)) =
      (∏ i : I, realPositionCharacter ds' i b) * absC b ^ (((n : ℕ) : ℂ) * c.exponent) := by
    have hχ' (i : I) : realPositionCharacter ds' i b =
        realPositionCharacter ds i b * (c0.character b : ℂ) :=
      realPositionCharacter_twistedPositionList ds c0 i b
    simp_rw [hχ', hcb, ← mul_assoc]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Complex.cpow_nat_mul]
  have hE : (fun s => torusEpsilon (fun i : I => RealBlockPosition.realPositionSign ds' i) *
      (∏ i : I, realPositionCharacter ds' i b) *
        absC b ^ (((n : ℕ) : ℂ) * (s + c.exponent - 1 / 2))) =
      fun s => torusEpsilon (fun i : I => RealBlockPosition.realPositionSign ds i + c.parity) *
        (∏ i : I, realPositionCharacter ds i b * (c.character b : ℂ)) *
        absC b ^ (((n : ℕ) : ℂ) * (s - 1 / 2)) := by
    funext s
    have hε : torusEpsilon (fun i : I => RealBlockPosition.realPositionSign ds' i) =
        torusEpsilon (fun i : I => RealBlockPosition.realPositionSign ds i + c.parity) := by
      unfold torusEpsilon
      exact Finset.prod_congr rfl fun i _ => by dsimp only; rw [he0]
    rw [hε, hprod, show ((n : ℕ) : ℂ) * (s + c.exponent - 1 / 2) =
      ((n : ℕ) : ℂ) * c.exponent + ((n : ℕ) : ℂ) * (s - 1 / 2) by ring, Complex.cpow_add _ _ hb]
    ring
  rw [hL, hLd, hE] at key
  exact key

end Langlands.GodementJacquet
