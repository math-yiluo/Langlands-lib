import Langlands.Global.RankinSelberg.ComplexLocalEqualUnfoldedSign
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient

/-! # The double integral in the complex equal-rank unfolding -/

noncomputable section

open MeasureTheory
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow_unipotent_mul unipotent_det)
open Langlands.QuotientIntegration
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "NG" => GeneralLinear.upperUnipotent n ℂ
local notation "QG" => LeftUnipotentQuotient (r + 1) ℂ
local notation "QH" => LeftUnipotentQuotient r ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "pad" => (padGL (R := ℂ) (Nat.le_succ (r + 1)))
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2

local instance complexUnfoldingMatrixSecondCountable (i : ℕ) :
    SecondCountableTopology (Matrix (Fin i) (Fin i) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin i → Fin i → ℂ))
local instance complexUnfoldingMatrixOppositeSecondCountable (i : ℕ) :
    SecondCountableTopology (Matrix (Fin i) (Fin i) ℂ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
local instance complexUnfoldingGLSecondCountable (i : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear i ℂ) :=
  Units.isInducing_embedProduct.secondCountableTopology
local instance complexUnfoldingMatrixLocallyCompact (i : ℕ) :
    LocallyCompactSpace (Matrix (Fin i) (Fin i) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin i → Fin i → ℂ))
local instance complexUnfoldingQuotientSigmaCompact (i : ℕ) :
    SigmaCompactSpace (LeftUnipotentQuotient i ℂ) := by
  have hq := leftQuotient_isOpenQuotientMap (GeneralLinear.upperUnipotent (i + 1) ℂ)
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

private def charDet {i : ℕ} (η : ℂˣ →* ℂˣ) (g : Langlands.GeneralLinear i ℂ) : ℂ :=
  (η (GeneralLinear.determinant g) : ℂ)

/-- Jacquet's rank recursion written with the large unipotent Haar integral.
The comparison to the rectangle-coordinate recursion requires the block Haar formula. -/
def complexEqualUnipotentRecursion (D : ComplexQuotientMeasureData (r + 1))
    (D₁ : ComplexQuotientMeasureData r) (η : ℂˣ →* ℂˣ) (a : ℂˣ)
    (Φ : Rect → ℂ) (U : H → ℂ) (g : G) : ℂ :=
  charDet η g * P g sm *
    ∫ q : QH, (∫ u : NG, Φ ((q.out⁻¹).val * complexSquareFirstRows (u.val * g).val) *
      complexWhittakerCharacter (-a) u.val ∂D.unipotentHaar) *
        U q.out * charDet η q.out⁻¹ * P q.out⁻¹ sn ∂D₁.measure

/-- The function on the large group before applying the padded-group change of variables. -/
def complexEqualUnfoldingGroupKernel (η : ℂˣ →* ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ) (q : QH) (g : G) : ℂ :=
  Φ ((q.out⁻¹).val * complexSquareFirstRows g.val) * φ (RankinSelberg.lastRow g) *
    V g * charDet η g * P g (s + sm) * U q.out * charDet η q.out⁻¹ * P q.out⁻¹ sn

/-- The product of the quotient kernel and the weighted square test after the substitution. -/
def complexEqualUnfoldingProductKernel (η : ℂˣ →* ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ) (p : QH × G) : ℂ :=
  complexSquareProductTest Φ φ p.2.val * charDet η p.2 * P p.2 (s + sm) *
    complexEqualUnfoldedInner U V p.2 s p.1

private theorem firstRows_pad_mul (h : H) (g : G) :
    complexSquareFirstRows (pad h * g).val = h.val * complexSquareFirstRows g.val := by
  ext i j
  change ((pad h).val * g.val) i.castSucc j = (h.val * complexSquareFirstRows g.val) i j
  simp only [Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc]
  have hlt (x : Fin m) : x.val ≤ r := Nat.le_of_lt_succ x.isLt
  simp [UnequalAnalytic.padGL_apply, hlt, Fin.castSucc_ne_last,
    complexSquareFirstRows]

private theorem lastRow_pad_mul (h : H) (g : G) :
    RankinSelberg.lastRow (pad h * g) = RankinSelberg.lastRow g := by
  funext j
  change ((pad h).val * g.val) (Fin.last m) j = g.val (Fin.last m) j
  conv_rhs => rw [← Matrix.one_mul g.val]
  simp only [Matrix.mul_apply, UnequalAnalytic.padGL_apply, Fin.val_last, lt_self_iff_false,
    false_and, dite_false]

private theorem det_pad (h : H) : GeneralLinear.determinant (pad h) = GeneralLinear.determinant h :=
  Units.ext (UnequalAnalytic.det_padGL _ _)

private theorem detPower_mul {i : ℕ} (g h : Langlands.GeneralLinear i ℂ) (s : ℂ) :
    P (g * h) s = P g s * P h s := by
  have hne (x : Langlands.GeneralLinear i ℂ) : ‖x.val.det‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (GeneralLinear.determinant x).ne_zero)
  simp only [ArchimedeanLocal.detPower, complexNormalizedAbs, Units.val_mul, Matrix.det_mul,
    norm_mul, mul_pow]
  rw [Real.log_mul (hne g) (hne h), Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem detPower_sub {i : ℕ} (g : Langlands.GeneralLinear i ℂ) (t u : ℂ) :
    P g t * P g⁻¹ u = P g (t - u) := by
  have hd : (g⁻¹ : Langlands.GeneralLinear i ℂ).val.det = g.val.det⁻¹ := by
    change (GeneralLinear.determinant g⁻¹ : ℂ) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  simp only [ArchimedeanLocal.detPower, hd, complexNormalizedAbs, norm_inv, inv_pow, Real.log_inv,
    Complex.ofReal_neg, ← Complex.exp_add]
  congr 1
  ring

private theorem groupKernel_pad (η : ℂˣ →* ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ) (q : QH) (g : G) :
    complexEqualUnfoldingGroupKernel η Φ φ U V s q (pad q.out * g) =
      complexEqualUnfoldingProductKernel η Φ φ U V s (q, g) := by
  have hrect : (q.out⁻¹).val * complexSquareFirstRows (pad q.out * g).val =
      complexSquareFirstRows g.val := by
    rw [firstRows_pad_mul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hχ : charDet η (pad q.out * g) * charDet η q.out⁻¹ = charDet η g := by
    have hd : GeneralLinear.determinant (pad q.out * g) * GeneralLinear.determinant q.out⁻¹ =
        GeneralLinear.determinant g := by
      simp only [map_mul, det_pad, map_inv]
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    unfold charDet
    rw [← Units.val_mul, ← map_mul, hd]
  have hpow : P (pad q.out * g) (s + sm) * P q.out⁻¹ sn =
      P g (s + sm) * P q.out (s - 1 / 2) := by
    have hp : P (pad q.out) (s + sm) = P q.out (s + sm) := by
      simp only [ArchimedeanLocal.detPower, UnequalAnalytic.det_padGL]
    rw [detPower_mul, hp, mul_right_comm, detPower_sub,
      show s + sm - sn = s - 1 / 2 by push_cast; ring]
    exact mul_comm _ _
  unfold complexEqualUnfoldingGroupKernel complexEqualUnfoldingProductKernel
  rw [hrect, lastRow_pad_mul]
  change _ = (Φ (complexSquareFirstRows g.val) * φ (RankinSelberg.lastRow g)) *
    charDet η g * P g (s + sm) * (U q.out * V (pad q.out * g) * P q.out (s - 1 / 2))
  calc
    _ = Φ (complexSquareFirstRows g.val) * φ (RankinSelberg.lastRow g) * U q.out *
        V (pad q.out * g) * (charDet η (pad q.out * g) * charDet η q.out⁻¹) *
          (P (pad q.out * g) (s + sm) * P q.out⁻¹ sn) := by ring
    _ = _ := by rw [hχ, hpow]; ring

variable (r) in
/-- The exact equal-rank integral agrees with (8.1), given the unipotent form of
the recursion and the absolute convergence needed for the two Fubini steps. -/
def ComplexLocalEqualUnfoldingStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (η : ℂˣ →* ℂˣ) (a : ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (W V : G → ℂ) (U : H → ℂ),
    (∀ g, W g = complexEqualUnipotentRecursion D D₁ η a Φ U g) →
    (∀ (u : NG) (g : G), V (u.val * g) = complexWhittakerCharacter (-a) u.val * V g) →
  ∀ s : ℂ,
    Integrable (fun p : QG × QH =>
      ∫ u : NG, complexEqualUnfoldingGroupKernel η Φ φ U V s p.2 (u.val * p.1.out)
        ∂D.unipotentHaar) (D.measure.prod D₁.measure) →
    (∀ᵐ q ∂D₁.measure, Integrable (complexEqualUnfoldingGroupKernel η Φ φ U V s q) D.groupHaar) →
    Integrable (complexEqualUnfoldingProductKernel η Φ φ U V s) (D₁.measure.prod D.groupHaar) →
    complexEqualIntegral D W V φ s =
      complexEqualUnfoldedIntegral D.groupHaar D₁ η (complexSquareProductTest Φ φ) U V s

theorem complexLocalEqualUnfolding : ComplexLocalEqualUnfoldingStatement r := by
  intro D D₁ η a Φ φ W V U hW hV s hJoint hGroup hProduct
  let : LocallyCompactSpace NG := GeneralLinear.UpperUnipotent.locallyCompactSpace
  let : SecondCountableTopology NG := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D₁.unipotentHaar.IsMulRightInvariant := D₁.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : D₁.measure.Regular := D₁.compatible.regular
  let F := complexEqualUnfoldingGroupKernel η Φ φ U V s
  let A := complexEqualUnfoldingProductKernel η Φ φ U V s
  let K (p : QG × QH) := ∫ u : NG, F p.2 (u.val * p.1.out) ∂D.unipotentHaar
  have hq (q : QG) : complexEqualIntegrand W V φ s q = ∫ k : QH, K (q, k) ∂D₁.measure := by
    let g := q.out
    let C := charDet η g * P g sm * V g * φ (RankinSelberg.lastRow g) * P g s
    let R (k : QH) (u : NG) :=
      Φ ((k.out⁻¹).val * complexSquareFirstRows (u.val * g).val) *
        complexWhittakerCharacter (-a) u.val
    change W g * V g * φ (RankinSelberg.lastRow g) * P g s = _
    calc
      _ = C * ∫ k : QH, (∫ u, R k u ∂D.unipotentHaar) *
          U k.out * charDet η k.out⁻¹ * P k.out⁻¹ sn ∂D₁.measure := by
        rw [hW, complexEqualUnipotentRecursion]
        dsimp only [C, R]
        ring
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun k => ?_
        change C * ((∫ u, R k u ∂D.unipotentHaar) * U k.out * charDet η k.out⁻¹ *
          P k.out⁻¹ sn) = ∫ u : NG, F k (u.val * g) ∂D.unipotentHaar
        simp only [← integral_mul_const, ← integral_const_mul]
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun u => ?_
        have hd : (u.val * g).val.det = g.val.det := by
          simp only [Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
        have hdu : GeneralLinear.determinant (u.val * g) = GeneralLinear.determinant g :=
          Units.ext hd
        simp only [C, R, F, complexEqualUnfoldingGroupKernel, hV, lastRow_unipotent_mul,
          charDet, hdu, ArchimedeanLocal.detPower, hd, add_mul, Complex.exp_add]
        ring
  calc
    complexEqualIntegral D W V φ s = ∫ q : QG, ∫ k : QH, K (q, k) ∂D₁.measure ∂D.measure :=
      integral_congr_ae (Filter.Eventually.of_forall hq)
    _ = ∫ p, K p ∂D.measure.prod D₁.measure := (integral_prod _ hJoint).symm
    _ = ∫ k : QH, ∫ q : QG, K (q, k) ∂D.measure ∂D₁.measure := integral_prod_symm _ hJoint
    _ = ∫ k : QH, ∫ g : G, F k g ∂D.groupHaar ∂D₁.measure := by
      apply integral_congr_ae
      filter_upwards [hGroup] with k hk
      exact Langlands.HarishChandraSchwartz.integral_integral_out_eq
        GeneralLinear.UpperUnipotent.isClosed D.compatible hk
    _ = ∫ k : QH, ∫ g : G, A (k, g) ∂D.groupHaar ∂D₁.measure := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun k => ?_
      change (∫ g, F k g ∂D.groupHaar) = ∫ g, A (k, g) ∂D.groupHaar
      rw [← integral_mul_left_eq_self (F k) (pad k.out)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
        groupKernel_pad η Φ φ U V s k g)
    _ = ∫ p, A p ∂D₁.measure.prod D.groupHaar := (integral_prod _ hProduct).symm
    _ = ∫ g : G, ∫ k : QH, A (k, g) ∂D₁.measure ∂D.groupHaar := integral_prod_symm _ hProduct
    _ = _ := by
      unfold complexEqualUnfoldedIntegral
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun g => ?_
      change (∫ k, (complexSquareProductTest Φ φ g.val * charDet η g * P g (s + sm)) *
        complexEqualUnfoldedInner U V g s k ∂D₁.measure) = _
      exact integral_const_mul _ _

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
