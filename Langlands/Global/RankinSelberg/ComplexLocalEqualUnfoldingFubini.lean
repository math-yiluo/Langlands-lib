import Langlands.Global.RankinSelberg.ComplexLocalEqualUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalParametricWeil
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight

/-! # The Weil and Fubini premises follow from the equal-rank product kernel -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.RankinSelberg
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexLocalIwasawa
open Langlands.GodementJacquet

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "QH" => LeftUnipotentQuotient r ℂ
local notation "QG" => LeftUnipotentQuotient (r + 1) ℂ
local notation "NH" => Langlands.GeneralLinear.upperUnipotent m ℂ
local notation "NG" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

private theorem firstRows_pad (h : H) (g : G) :
    complexSquareFirstRows (pad h * g).val = h.val * complexSquareFirstRows g.val := by
  ext i j
  change ((pad h).val * g.val) i.castSucc j = (h.val * complexSquareFirstRows g.val) i j
  simp only [Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc]
  have hlt (x : Fin m) : x.val ≤ r := Nat.le_of_lt_succ x.isLt
  simp [UnequalAnalytic.padGL_apply, hlt, Fin.castSucc_ne_last, complexSquareFirstRows]

private theorem lastRow_pad (h : H) (g : G) :
    RankinSelberg.lastRow (pad h * g) = RankinSelberg.lastRow g := by
  funext j
  change ((pad h).val * g.val) (Fin.last m) j = g.val (Fin.last m) j
  conv_rhs => rw [← Matrix.one_mul g.val]
  simp only [Matrix.mul_apply, UnequalAnalytic.padGL_apply, Fin.val_last, lt_self_iff_false,
    false_and, dite_false]

/-- Padding a leading upper-unipotent block gives an upper-unipotent element. -/
theorem complexEqualPad_mem_upperUnipotent (u : NH) : pad u.val ∈ NG := by
  constructor
  · intro i j hij
    change j < i at hij
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_eq_zero u hij
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_diag u _
    · exact Matrix.one_apply_eq i

private theorem shiftedGroupKernel (η : ℂˣ →* ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ) (q : QH) (g : G) :
    complexEqualUnfoldingGroupKernel η Φ φ U V s q g =
      complexEqualUnfoldingProductKernel η Φ φ U V s (q, (pad q.out)⁻¹ * g) := by
  let h := q.out
  let t := s + ((m : ℕ) : ℂ) / 2
  let u := ((n : ℕ) : ℂ) / 2
  let k := (pad h)⁻¹ * g
  have hk : pad h * k = g := by
    dsimp only [k]
    exact mul_inv_cancel_left _ _
  have hrect : (h⁻¹).val * complexSquareFirstRows g.val = complexSquareFirstRows k.val := by
    rw [← hk, firstRows_pad, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  have hrow : RankinSelberg.lastRow g = RankinSelberg.lastRow k := by
    exact congrArg RankinSelberg.lastRow hk.symm |>.trans (lastRow_pad h k)
  have hdet : determinant g * determinant h⁻¹ = determinant k := by
    have hp : determinant (pad h) = determinant h := Units.ext (UnequalAnalytic.det_padGL _ _)
    have hg : determinant g = determinant h * determinant k := calc
      determinant g = determinant (pad h * k) := congrArg determinant hk.symm
      _ = _ := by rw [map_mul, hp]
    rw [hg,
      mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hχ : (η (determinant g) : ℂ) * (η (determinant h⁻¹) : ℂ) =
      (η (determinant k) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, hdet]
  have hPow : P g t * P h⁻¹ u = P k t * P h (s - 1 / 2) := by
    have hp : P (pad h) t = P h t := by simp only [ArchimedeanLocal.detPower, UnequalAnalytic.det_padGL]
    rw [show P g t = P h t * P k t by rw [← hp, ← detPower_complex_mul, hk],
      mul_right_comm, detPower_complex_inv,
      ← detPower_complex_add]
    have ht : t + -u = s - 1 / 2 := by
      dsimp [t, u]
      push_cast
      ring
    rw [ht, mul_comm]
  change Φ ((h⁻¹).val * complexSquareFirstRows g.val) * φ (RankinSelberg.lastRow g) * V g *
      (η (determinant g) : ℂ) * P g t * U h * (η (determinant h⁻¹) : ℂ) * P h⁻¹ u =
    complexSquareProductTest Φ φ k.val * (η (determinant k) : ℂ) * P k t *
      (U h * V (pad h * k) * P h (s - 1 / 2))
  rw [hrect, hrow, hk]
  change _ = (Φ (complexSquareFirstRows k.val) * φ (RankinSelberg.lastRow k)) *
    (η (determinant k) : ℂ) * P k t * (U h * V g * P h (s - 1 / 2))
  calc
    _ = Φ (complexSquareFirstRows k.val) * φ (RankinSelberg.lastRow k) * U h * V g *
        ((η (determinant g) : ℂ) * (η (determinant h⁻¹) : ℂ)) * (P g t * P h⁻¹ u) := by ring
    _ = _ := by rw [hχ, hPow]; ring

private theorem quotient_out_eq_unipotent_mul {j : ℕ} (q : LeftUnipotentQuotient j ℂ) :
    ∃ u : Langlands.GeneralLinear.upperUnipotent (j + 1) ℂ,
      q.out = u.val * quotientRepresentative q := by
  have he : Quotient.mk _ (quotientRepresentative q) = Quotient.mk _ q.out :=
    (mk_quotientRepresentative q).trans (Quotient.out_eq q).symm
  have hu := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  exact ⟨⟨q.out * (quotientRepresentative q)⁻¹, hu⟩, (inv_mul_cancel_right _ _).symm⟩

private def quotientLeftShear : QH × G ≃ᵐ QH × G where
  toFun p := (p.1, (pad (quotientRepresentative p.1))⁻¹ * p.2)
  invFun p := (p.1, pad (quotientRepresentative p.1) * p.2)
  left_inv := by rintro ⟨q, g⟩; simp only [mul_inv_cancel_left]
  right_inv := by rintro ⟨q, g⟩; simp only [inv_mul_cancel_left]
  measurable_toFun := measurable_fst.prodMk
    ((((UnequalAnalytic.continuous_padGL _).comp continuous_quotientRepresentative).measurable.comp
      measurable_fst).inv.mul measurable_snd)
  measurable_invFun := measurable_fst.prodMk
    ((((UnequalAnalytic.continuous_padGL _).comp continuous_quotientRepresentative).measurable.comp
      measurable_fst).mul measurable_snd)

/-- Once the shifted product kernel is continuous and integrable, the Fubini and
Weil premises of the equal-rank unfolding follow. -/
def ComplexLocalEqualUnfoldingFubiniStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (η : ℂˣ →* ℂˣ) (a : ℂˣ) (Φ : Rect → ℂ) (φ : Row → ℂ)
    (W V : G → ℂ) (U : H → ℂ),
    (∀ g, W g = complexEqualUnipotentRecursion D D₁ η a Φ U g) →
    (∀ (u : NG) (g : G), V (u.val * g) = complexWhittakerCharacter (-a) u.val * V g) →
  ∀ s : ℂ, Continuous (complexEqualUnfoldingProductKernel η Φ φ U V s) →
    Integrable (complexEqualUnfoldingProductKernel η Φ φ U V s) (D₁.measure.prod D.groupHaar) →
    complexEqualIntegral D W V φ s =
      complexEqualUnfoldedIntegral D.groupHaar D₁ η (complexSquareProductTest Φ φ) U V s

set_option maxHeartbeats 1600000 in
theorem complexLocalEqualUnfoldingFubini : ComplexLocalEqualUnfoldingFubiniStatement (r := r) := by
  intro D D₁ η a Φ φ W V U hW hV s hAc hProd
  let : SecondCountableTopology G := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := inferInstance
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D₁.unipotentHaar.IsMulRightInvariant := D₁.unipotentHaar_rightInvariant
  let : SigmaCompactSpace QH := (quotientHomeomorph m).isClosedEmbedding.sigmaCompactSpace
  let : D₁.measure.Regular := D₁.compatible.regular
  let : SigmaFinite D₁.measure := inferInstance
  let A := complexEqualUnfoldingProductKernel η Φ φ U V s
  let F := complexEqualUnfoldingGroupKernel η Φ φ U V s
  let e := quotientLeftShear (r := r)
  have hMP : MeasurePreserving e (D₁.measure.prod D.groupHaar) (D₁.measure.prod D.groupHaar) :=
    (MeasurePreserving.id D₁.measure).skew_product e.measurable.snd
      (Filter.Eventually.of_forall fun q =>
        (measurePreserving_mul_left D.groupHaar (pad (quotientRepresentative q))⁻¹).map_eq)
  let B := A ∘ e
  have hBi : Integrable B (D₁.measure.prod D.groupHaar) :=
    (hMP.integrable_comp_emb e.measurableEmbedding).mpr hProd
  have hBm : Measurable B := hAc.measurable.comp e.measurable
  have hGroup : ∀ᵐ q ∂D₁.measure, Integrable (F q) D.groupHaar := by
    filter_upwards [hProd.prod_right_ae] with q hq
    let l := Homeomorph.mulLeft (pad q.out)⁻¹
    have hl : MeasurePreserving l D.groupHaar D.groupHaar := measurePreserving_mul_left _ _
    refine ((hl.integrable_comp_emb l.toMeasurableEquiv.measurableEmbedding).mpr hq).congr
      (ae_of_all _ fun g => ?_)
    exact (shiftedGroupKernel η Φ φ U V s q g).symm
  have hJ := complexLocalParametricWeil QH D₁.measure D B hBm hBi
  have hJoint : Integrable (fun p : QG × QH => ∫ u : NG, F p.2 (u.val * p.1.out) ∂D.unipotentHaar)
      (D.measure.prod D₁.measure) := by
    refine hJ.congr (ae_of_all _ ?_)
    rintro ⟨q, k⟩
    obtain ⟨u, hu⟩ := quotient_out_eq_unipotent_mul k
    obtain ⟨v, hv⟩ := quotient_out_eq_unipotent_mul q
    let uG : NG := ⟨pad u.val, complexEqualPad_mem_upperUnipotent u⟩
    let J (w : NG) := B (k, w.val * quotientRepresentative q)
    change (∫ w, J w ∂D.unipotentHaar) = ∫ w : NG, F k (w.val * q.out) ∂D.unipotentHaar
    symm
    calc
      _ = ∫ w : NG, J ((uG⁻¹ * w) * v) ∂D.unipotentHaar := by
        refine integral_congr_ae (ae_of_all _ fun w => ?_)
        change F k (w.val * q.out) = J ((uG⁻¹ * w) * v)
        rw [show F k (w.val * q.out) = A (k, (pad k.out)⁻¹ * (w.val * q.out)) from
          shiftedGroupKernel η Φ φ U V s k _]
        change A (k, (pad k.out)⁻¹ * (w.val * q.out)) =
          A (k, (pad (quotientRepresentative k))⁻¹ *
            (((uG⁻¹ * w) * v).val * quotientRepresentative q))
        simp only [hu, hv, map_mul, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, uG, mul_assoc]
      _ = ∫ w : NG, J (w * v) ∂D.unipotentHaar :=
        integral_mul_left_eq_self (fun w => J (w * v)) uG⁻¹
      _ = _ := integral_mul_right_eq_self J v
  exact complexLocalEqualUnfolding (r := r) D D₁ η a Φ φ W V U hW hV s hJoint hGroup hProd

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
