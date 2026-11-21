import Langlands.Global.RankinSelberg.RealLocalAdjacentUnfolding
import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Global.RankinSelberg.RealLocalWhittakerChangeCharacter
import Langlands.Global.RankinSelberg.RealMatrixConvergence

/-! # Absolute convergence of the real unfolded corank-one kernel -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap ENNReal NNReal
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.QuotientIntegration
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
open Langlands.Archimedean (unitaryCompact)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Rows" => Fin (r + 1) → ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance adjacentConvMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance adjacentConvGLSecondCountable : SecondCountableTopology H :=
  (Units.isOpenEmbedding_val (R := Mat)).isInducing.secondCountableTopology
local instance adjacentConvMatrixLocallyCompact : LocallyCompactSpace Mat :=
  inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance adjacentConvQuotientSigmaCompact : SigmaCompactSpace Q := by
  have hq := leftQuotient_isOpenQuotientMap N
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

private theorem norm_realCharacter (c : RealCharacterData) (x : ℝˣ) :
    ‖(c.character x : ℂ)‖ = |(x : ℝ)| ^ c.exponent.re := by
  have hx : 0 < |(x : ℝ)| := abs_pos.mpr x.ne_zero
  have h1 : ‖((((x : ℝ) / |(x : ℝ)| : ℝ)) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self hx.ne']
  rw [c.character_eq, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, h1, one_pow,
    one_mul]

/-- The norm of the matrix weight is the Schwartz norm times one real determinant power. -/
private theorem norm_matrixWeight (c : RealCharacterData) (F : Mat → ℂ) (s : ℂ) (z : H) :
    ‖realAdjacentMatrixWeight c.character.toMonoidHom F s z‖ =
      ‖F z.val‖ * |z.val.det| ^ (s.re + (r : ℝ) / 2 + c.exponent.re) := by
  have hA : 0 < |z.val.det| := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero z)
  have hd : ((GeneralLinear.determinant z : ℝˣ) : ℝ) = z.val.det := rfl
  unfold realAdjacentMatrixWeight detCharacter
  rw [norm_mul, norm_mul, Langlands.GodementJacquet.norm_realDetPower]
  change ‖F z.val‖ * ‖(c.character (GeneralLinear.determinant z) : ℂ)‖ * _ = _
  rw [norm_realCharacter, hd, mul_assoc, ← Real.rpow_add hA]
  congr 2
  have hre : (s + (r : ℂ) / 2).re = s.re + (r : ℝ) / 2 := by simp
  rw [hre]
  ring

/-- The equal-rank part of the unfolded kernel at a quotient class. -/
private def innerKernel (U V : H → ℂ) (f : Rows → ℂ) (s : ℂ) (z g : H) : ℂ :=
  kernel U (fun x => V (x * z)) f g * Complex.exp (s * (logDet g : ℂ))

private theorem innerKernel_unipotent {U V : H → ℂ} (f : Rows → ℂ) (s : ℂ)
    (hinv : ∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z)) (z : H)
    (u : N) (g : H) : innerKernel U V f s z (u.val * g) = innerKernel U V f s z g := by
  unfold innerKernel
  rw [kernel_unipotent_mul (W' := fun x => V (x * z)) (fun u hu g => hinv u hu g z) u g,
    logDet_unipotent_mul u g]

private theorem unfoldedKernel_eq (c : RealCharacterData) (F : Mat → ℂ) (f : Rows → ℂ)
    (U V : H → ℂ) (s : ℂ) (p : Q × H) :
    realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s p =
      innerKernel U V f s p.2 p.1.out * realAdjacentMatrixWeight c.character.toMonoidHom F s p.2 :=
  rfl

private theorem continuous_innerKernel {U V : H → ℂ} {f : Rows → ℂ} (s : ℂ)
    (hU : Continuous U) (hV : Continuous V) (hf : Continuous f) :
    Continuous (fun p : H × H => innerKernel U V f s p.2 p.1) := by
  have hrow : Continuous (lastRow : H → Rows) :=
    continuous_pi fun j => (Langlands.GeneralLinear.entry (Fin.last r) j).continuous
  unfold innerKernel kernel
  exact (((hU.comp continuous_fst).mul (hV.comp (continuous_fst.mul continuous_snd))).mul
    (hf.comp (hrow.comp continuous_fst))).mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_logDet.comp continuous_fst))))

private theorem continuous_matrixWeight (c : RealCharacterData) (F : 𝓢(Mat, ℂ)) (s : ℂ) :
    Continuous (realAdjacentMatrixWeight (r := r) c.character.toMonoidHom F s) := by
  have hval : Continuous (fun g : H => g.val.det) := Units.continuous_val.matrix_det
  have hdet : Continuous (fun z : H => GeneralLinear.determinant z) := by
    refine Units.continuous_iff.mpr ⟨hval, ?_⟩
    simp only [← map_inv]
    change Continuous (fun g : H => (g⁻¹).val.det)
    exact hval.comp continuous_inv
  unfold realAdjacentMatrixWeight detCharacter
  refine ((F.continuous.comp Units.continuous_val).mul ?_).mul ?_
  · exact Units.continuous_val.comp (c.character.continuous.comp hdet)
  · exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_logDet (r := r))))

/-- The unfolded corank-one kernel of Jacquet's (8.3) is absolutely integrable on a right
half-plane, for a gauge-bounded first function and a polynomially bounded second function
whose product is unipotent invariant. -/
def RealAdjacentConvergenceStatement : Prop :=
  ∀ (D : RealQuotientMeasureData r) (c : RealCharacterData) (F : 𝓢(Mat, ℂ)) (f : Rows → ℂ)
    (U V : H → ℂ),
    Continuous U → Continuous V → Continuous f → HasRapidDecay f →
    (∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z)) →
    HasGauge U → (∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s)
        (D.measure.prod D.groupHaar)

set_option maxHeartbeats 800000 in
theorem realAdjacentConvergence : RealAdjacentConvergenceStatement (r := r) := by
  intro D c F f U V hU hV hf hfd hinv hgU hVg
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  obtain ⟨κ, L, hκL⟩ := exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  obtain ⟨N₁, hN₁⟩ := hgU
  obtain ⟨C₂, M₂, hC₂, hV₂⟩ := hVg
  let A : ℝ := (N₁ : ℝ) + ((2 * M₂ : ℕ) : ℝ)
  have hA : 0 ≤ A := by positivity
  let σ₁ : ℝ := (A + ‖L‖ + 1) * ((r : ℝ) + 1)
  let σ₂ : ℝ := (r : ℝ) + 1 + 2 * (M₂ : ℝ) - (r : ℝ) / 2 - c.exponent.re
  refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
  let t : ℝ := s.re
  have ht : (A + ‖L‖ + 1) * ((r : ℝ) + 1) ≤ t := ((le_max_left _ _).trans_lt hs).le
  have ht₂ : σ₂ ≤ t := ((le_max_right _ _).trans_lt hs).le
  let M : ℕ := ⌈(A + ‖L‖ + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1)⌉₊
  obtain ⟨C₁, hC₁, hU₁⟩ := hN₁ M
  obtain ⟨C₃, hC₃, hf₃⟩ := exists_norm_le_exp hfd (c := (r : ℝ) + 1) (by positivity) M
  let H₀ : ℝ := (2 * ((r : ℝ) + 1) ^ 2) ^ M₂
  let C : ℝ := C₁ * (C₂ * H₀) * C₃
  have hC : 0 ≤ C := by positivity
  let E (y : Rows) : ℝ := -(M : ℝ) * rootPos y + A * ∑ j, |y j| + t * ∑ j, y j -
    (M : ℝ) * max (y (Fin.last r)) 0
  have hEc : Continuous E := by
    have h1 : Continuous fun y : Rows => ∑ j, |y j| :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).abs
    have h2 : Continuous fun y : Rows => ∑ j, y j :=
      continuous_finsetSum _ fun j _ => continuous_apply j
    exact (((continuous_const.mul continuous_rootPos).add (continuous_const.mul h1)).add
      (continuous_const.mul h2)).sub
      (continuous_const.mul ((continuous_apply _).max continuous_const))
  let Q₀ (q : Q) : ℝ := C * Real.exp (E (alphaQ q))
  have hQ₀c : Continuous Q₀ := continuous_const.mul (Real.continuous_exp.comp (hEc.comp continuous_alphaQ))
  have hQ : Integrable Q₀ D.measure :=
    integrable_of_toral_bound hκL hQ₀c.aestronglyMeasurable hC hA ht (Nat.le_ceil _)
      (Nat.le_ceil _) fun q => by
        rw [Real.norm_of_nonneg (by positivity)]
  let qe : ℝ := t + (r : ℝ) / 2 + c.exponent.re
  let hgt (z : H) : ℂ := ((realMatrixHeight z ^ M₂ : ℝ) : ℂ)
  have hgtm : Measurable hgt := by
    have hH : Continuous (fun g : H => realMatrixHeight g) := by
      unfold realMatrixHeight
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((Units.continuous_val.matrix_elem i j).norm.pow 2).add
          ((Units.continuous_coe_inv.matrix_elem i j).norm.pow 2)
    exact (Complex.continuous_ofReal.comp (hH.pow M₂)).measurable
  have hgtb (z : H) : ‖hgt z‖ ≤ 1 * realMatrixHeight z ^ M₂ := by
    rw [one_mul, Complex.norm_real, Real.norm_of_nonneg
      (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg z) _)]
  have hqe : (r : ℝ) + 1 + 2 * M₂ ≤ qe := by
    dsimp only [qe]
    dsimp only [σ₂] at ht₂
    linarith
  have hP : Integrable (fun z : H => ‖F z.val‖ * ‖hgt z‖ * |z.val.det| ^ qe) D.groupHaar :=
    Langlands.GodementJacquet.integrable_realMatrixWeightedNorm D.groupHaar hgtm F zero_le_one
      hgtb hqe
  have hbound (p : Q × H) :
      ‖realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s p‖ ≤
        Q₀ p.1 * (‖F p.2.val‖ * ‖hgt p.2‖ * |p.2.val.det| ^ qe) := by
    rcases p with ⟨q, z⟩
    let y := alphaQ q
    let k := kpart q.out
    let x : H := torus y * (k : H)
    have hx : innerKernel U V f s z q.out = innerKernel U V f s z x := by
      rw [eq_torus_mul_kpart (innerKernel U V f s z) (innerKernel_unipotent f s hinv z) q.out,
        alpha_out q]
    have hgt0 : 0 ≤ realMatrixHeight z := RealPlaceRestriction.realMatrixHeight_nonneg z
    have hVx : ‖V (x * z)‖ ≤ C₂ * H₀ * Real.exp (((2 * M₂ : ℕ) : ℝ) * ∑ j, |y j|) *
        realMatrixHeight z ^ M₂ := by
      have hxz := RealCharacterChange.realMatrixHeight_mul_le x z
      have hxh := RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le y k M₂
      calc
        ‖V (x * z)‖ ≤ C₂ * realMatrixHeight (x * z) ^ M₂ := hV₂ _
        _ ≤ C₂ * (realMatrixHeight x ^ M₂ * realMatrixHeight z ^ M₂) := by
          rw [← mul_pow]
          gcongr
          exact RealPlaceRestriction.realMatrixHeight_nonneg _
        _ ≤ C₂ * ((H₀ * Real.exp (((2 * M₂ : ℕ) : ℝ) * ∑ j, |y j|)) *
            realMatrixHeight z ^ M₂) := by gcongr
        _ = _ := by ring
    have hUx := hU₁ y k
    have hfx := hf₃ (lastRow x) (y (Fin.last r)) (exp_le_mul_norm_lastRow y k)
    have hlog : logDet x = ∑ j, y j := logDet_torus_mul y k
    have hinner : ‖innerKernel U V f s z x‖ ≤ C * Real.exp (E y) * realMatrixHeight z ^ M₂ := by
      unfold innerKernel kernel
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, hlog]
      have hre : (s * ((∑ j, y j : ℝ) : ℂ)).re = t * ∑ j, y j := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, t]
      rw [hre]
      calc
        ‖U x‖ * ‖V (x * z)‖ * ‖f (lastRow x)‖ * Real.exp (t * ∑ j, y j) ≤
            (C₁ * Real.exp (-(M : ℝ) * rootPos y + (N₁ : ℝ) * ∑ j, |y j|)) *
              (C₂ * H₀ * Real.exp (((2 * M₂ : ℕ) : ℝ) * ∑ j, |y j|) *
                realMatrixHeight z ^ M₂) *
              (C₃ * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0)) *
              Real.exp (t * ∑ j, y j) := by
          gcongr
        _ = C * Real.exp (E y) * realMatrixHeight z ^ M₂ := by
          have hE : E y = (-(M : ℝ) * rootPos y + (N₁ : ℝ) * ∑ j, |y j|) +
              ((2 * M₂ : ℕ) : ℝ) * ∑ j, |y j| + (-(M : ℝ) * max (y (Fin.last r)) 0) +
              t * ∑ j, y j := by
            simp only [E, A]
            ring
          rw [hE]
          simp only [C, Real.exp_add]
          ring
    rw [unfoldedKernel_eq, norm_mul, hx, norm_matrixWeight]
    have hnh : ‖hgt z‖ = realMatrixHeight z ^ M₂ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hgt0 _)]
    rw [hnh]
    change _ ≤ C * Real.exp (E y) * (‖F z.val‖ * realMatrixHeight z ^ M₂ * |z.val.det| ^ qe)
    calc
      ‖innerKernel U V f s z x‖ * (‖F z.val‖ * |z.val.det| ^ (s.re + (r : ℝ) / 2 + c.exponent.re))
          ≤ (C * Real.exp (E y) * realMatrixHeight z ^ M₂) *
            (‖F z.val‖ * |z.val.det| ^ (s.re + (r : ℝ) / 2 + c.exponent.re)) := by
        gcongr
      _ = _ := by
        simp only [qe, t]
        ring
  have hmeas : AEStronglyMeasurable
      (realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s) (D.measure.prod D.groupHaar) := by
    have HQ := leftQuotient_isOpenQuotientMap N
    have hcont : Continuous (realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s) := by
      rw [← (HQ.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
      have hEq : realAdjacentUnfoldedKernel c.character.toMonoidHom F f U V s ∘
          Prod.map (leftQuotientMap N) id = fun p : H × H =>
            innerKernel U V f s p.2 p.1 * realAdjacentMatrixWeight c.character.toMonoidHom F s p.2 := by
        funext p
        rcases p with ⟨g, z⟩
        change innerKernel U V f s z (leftQuotientMap N g).out * _ = _
        rw [RealEqualConvergence.out_eq_descend (innerKernel U V f s z)
          (innerKernel_unipotent f s hinv z), leftQuotientMap_apply,
          Langlands.QuotientIntegration.descend_mk]
        rfl
      rw [hEq]
      exact (continuous_innerKernel s hU hV hf).mul ((continuous_matrixWeight c F s).comp continuous_snd)
    exact hcont.aestronglyMeasurable
  exact (hQ.mul_prod hP).mono' hmeas (ae_of_all _ fun p => by simpa only [mul_assoc] using hbound p)

end Langlands.Global.RankinSelbergGlobal.RealJacquet
