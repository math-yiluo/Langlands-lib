import Langlands.Global.RankinSelberg.RealGodementHaar
import Langlands.Global.RankinSelberg.RealPlaceEqualReflection
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear

/-! # Quotient change of variables in the real adjacent-rank integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator
open Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "gap" => Nat.lt_succ_self r
local notation "G" => Langlands.GeneralLinear (r + 2) ℝ
local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Rows" => Fin (r + 1) → ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance adjacentMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance adjacentGLSecondCountable : SecondCountableTopology H :=
  (Units.isOpenEmbedding_val (R := Mat)).isInducing.secondCountableTopology
local instance adjacentMatrixLocallyCompact : LocallyCompactSpace Mat :=
  inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance adjacentQuotientSigmaCompact : SigmaCompactSpace Q := by
  have hq := leftQuotient_isOpenQuotientMap N
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

/-- The real determinant power is multiplicative in the group variable. -/
theorem realDetPower_mul {n : ℕ} (g k : Langlands.GeneralLinear n ℝ) (s : ℂ) :
    P (g * k) s = P g s * P k s := by
  have hne (x : Langlands.GeneralLinear n ℝ) : |x.val.det| ≠ 0 :=
    abs_ne_zero.mpr (GeneralLinear.determinant x).ne_zero
  simp only [ArchimedeanLocal.detPower, realNormalizedAbs, Units.val_mul, Matrix.det_mul, abs_mul]
  rw [Real.log_mul (hne g) (hne k), Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem detPower_add (g : H) (s t : ℂ) : P g (s + t) = P g s * P g t := by
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

/-- An actual character of real units evaluated at the determinant. -/
def detCharacter (η : ℝˣ →* ℂˣ) {n : ℕ} (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  (η (GeneralLinear.determinant g) : ℂ)

theorem detCharacter_mul (η : ℝˣ →* ℂˣ) {n : ℕ} (g k : Langlands.GeneralLinear n ℝ) :
    detCharacter η (g * k) = detCharacter η g * detCharacter η k := by
  simp only [detCharacter, map_mul, Units.val_mul]

/-- The smaller-group kernel for restriction of the recursive Whittaker coefficient
following a partial transform in the free column. -/
def realAdjacentRestrictionKernel (η : ℝˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U : H → ℂ) (g k : H) : ℂ :=
  detCharacter η g * P g (((r + 1 : ℕ) : ℂ) / 2) *
    Φ₁ (k⁻¹ * g).val * Φ₂ (lastRow k) * U k * detCharacter η k⁻¹ * P k⁻¹ ((r : ℂ) / 2)

/-- The matrix test with the actual determinant twist and the corank-one spectral shift. -/
def realAdjacentMatrixWeight (η : ℝˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (s : ℂ) (z : H) : ℂ :=
  Φ₁ z.val * detCharacter η z * P z (s + (r : ℂ) / 2)

/-- The joint quotient and matrix kernel after the change of variables. -/
def realAdjacentUnfoldedKernel (η : ℝˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U V : H → ℂ) (s : ℂ) (p : Q × H) : ℂ :=
  realEqualIntegrand U (fun x => V (x * p.2)) Φ₂ s p.1 * realAdjacentMatrixWeight η Φ₁ s p.2

/-- The unfolded matrix integral of smaller equal-rank integrals. -/
def realAdjacentUnfoldedIntegral (D : RealQuotientMeasureData r) (η : ℝˣ →* ℂˣ)
    (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ) (U V : H → ℂ) (s : ℂ) : ℂ :=
  ∫ z : H, realEqualIntegral D U (fun x => V (x * z)) Φ₂ s *
    realAdjacentMatrixWeight η Φ₁ s z ∂D.groupHaar

private theorem realEqualIntegrand_mk (U V : H → ℂ)
    (hUV : ∀ (u : N) (g : H), U (u.val * g) * V (u.val * g) = U g * V g)
    (Φ₂ : Rows → ℂ) (s : ℂ) (g : H) :
    realEqualIntegrand U V Φ₂ s (Quotient.mk _ g) = U g * V g * Φ₂ (lastRow g) * P g s := by
  let f := RealPlaceReflection.kernel (fun k => U k * V k) Φ₂ s
  let F := descend N f (RealPlaceReflection.kernel_unipotent_mul _ hUV Φ₂ s)
  have h := congrArg F (Quotient.out_eq (Quotient.mk _ g : Q))
  exact h

private theorem restrictionKernel_change (η : ℝˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U V : H → ℂ)
    (hUV : ∀ (z : H) (u : N) (g : H), U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z))
    (s : ℂ) (q : Q) (z : H) :
    realAdjacentRestrictionKernel η Φ₁ Φ₂ U q.out (q.out * z⁻¹) * V q.out * P q.out (s - 1 / 2) =
      realAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s ((rightQuotientShear N).symm (q, z)) := by
  let g := q.out
  let k := g * z⁻¹
  have hk : k * z = g := by simp [k]
  have hkg : k⁻¹ * g = z := by rw [← hk, inv_mul_cancel_left]
  have hq : ((rightQuotientShear N).symm (q, z)).1 = Quotient.mk _ k := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hχ : detCharacter η g * detCharacter η k⁻¹ = detCharacter η z := by
    rw [mul_comm, ← detCharacter_mul, hkg]
  have hP : P g (((r + 1 : ℕ) : ℂ) / 2) * P k⁻¹ ((r : ℂ) / 2) * P g (s - 1 / 2) =
      P k s * P z (s + (r : ℂ) / 2) := by
    calc
      _ = P k⁻¹ ((r : ℂ) / 2) * P g ((r : ℂ) / 2) * P g s := by
        rw [mul_right_comm, ← detPower_add, show (((r + 1 : ℕ) : ℂ) / 2) + (s - 1 / 2) =
          (r : ℂ) / 2 + s by push_cast; ring, detPower_add]
        ring
      _ = P z ((r : ℂ) / 2) * (P k s * P z s) := by
        rw [← realDetPower_mul, hkg, ← realDetPower_mul, hk]
      _ = _ := by rw [detPower_add]; ring
  unfold realAdjacentUnfoldedKernel
  change _ = realEqualIntegrand U (fun x => V (x * z)) Φ₂ s
        ((rightQuotientShear N).symm (q, z)).1 *
    (Φ₁ z.val * detCharacter η z * P z (s + (r : ℂ) / 2))
  rw [hq, realEqualIntegrand_mk U (fun x => V (x * z)) (hUV z), hk]
  change detCharacter η g * P g (((r + 1 : ℕ) : ℂ) / 2) *
      Φ₁ (k⁻¹ * g).val * Φ₂ (lastRow k) * U k * detCharacter η k⁻¹ * P k⁻¹ ((r : ℂ) / 2) *
      V g * P g (s - 1 / 2) = _
  rw [hkg]
  calc
    _ = U k * V g * Φ₂ (lastRow k) * Φ₁ z.val *
          (detCharacter η g * detCharacter η k⁻¹) *
          (P g (((r + 1 : ℕ) : ℂ) / 2) * P k⁻¹ ((r : ℂ) / 2) * P g (s - 1 / 2)) := by ring
    _ = _ := by rw [hχ, hP]; ring

/-- The real corank-one unfolding, given the restricted recursive formula and absolute
convergence of the resulting joint kernel at the spectral value. -/
def RealLocalAdjacentUnfoldingStatement (r : ℕ) : Prop :=
  ∀ (D : RealQuotientMeasureData r) (η : ℝˣ →* ℂˣ)
    (Φ₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (Φ₂ : (Fin (r + 1) → ℝ) → ℂ)
    (W : Langlands.GeneralLinear (r + 2) ℝ → ℂ)
    (U V : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    (∀ (z : Langlands.GeneralLinear (r + 1) ℝ) (u : GeneralLinear.upperUnipotent (r + 1) ℝ)
      (g : Langlands.GeneralLinear (r + 1) ℝ),
      U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z)) →
    ∀ b : ℂ, (∀ g : Langlands.GeneralLinear (r + 1) ℝ,
      W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) = b *
        ∫ k, realAdjacentRestrictionKernel η Φ₁ Φ₂ U g k ∂D.groupHaar) →
    ∀ s : ℂ, Integrable (realAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s) (D.measure.prod D.groupHaar) →
      realUnequalIntegral (Nat.lt_succ_self r) D W V s =
        b * realAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s

theorem realLocalAdjacentUnfolding : RealLocalAdjacentUnfoldingStatement r := by
  intro D η Φ₁ Φ₂ W U V hUV b hW s hInt
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.groupHaar.IsInvInvariant := (RealGodement.realMatrixHaar_symmetries D.groupHaar).2
  let : D.measure.Regular := D.compatible.regular
  let F := realAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s
  let e := (rightQuotientShear N).symm
  have he : MeasurePreserving e (D.measure.prod D.groupHaar) (D.measure.prod D.groupHaar) :=
    measurePreserving_rightQuotientShear_symm N D.measure D.groupHaar D.compatible.right_invariant
  have hBefore : Integrable (fun p => F (e p)) (D.measure.prod D.groupHaar) :=
    (he.integrable_comp_emb e.toMeasurableEquiv.measurableEmbedding).mpr hInt
  calc
    realUnequalIntegral gap D W V s =
        b * ∫ q : Q, ∫ z : H, F (e (q, z)) ∂D.groupHaar ∂D.measure := by
      change (∫ q, realUnequalIntegrand gap W V s q ∂D.measure) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      have hshift : (r + 1 - r : ℕ) = 1 := by omega
      simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hshift, Nat.cast_one, hW,
        mul_assoc b, ← integral_mul_const]
      congr 1
      let g := q.out
      let e₁ := (Homeomorph.inv H).trans (Homeomorph.mulLeft g)
      have he₁ : MeasurePreserving e₁ D.groupHaar D.groupHaar :=
        Measure.measurePreserving_div_left D.groupHaar g
      rw [← he₁.integral_comp e₁.toMeasurableEquiv.measurableEmbedding]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
        restrictionKernel_change η Φ₁ Φ₂ U V hUV s q z)
    _ = b * ∫ p, F (e p) ∂D.measure.prod D.groupHaar :=
      congrArg (b * ·) (integral_prod _ hBefore).symm
    _ = b * ∫ p, F p ∂D.measure.prod D.groupHaar :=
      congrArg (b * ·) (he.integral_comp e.toMeasurableEquiv.measurableEmbedding F)
    _ = b * realAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s := by
      unfold realAdjacentUnfoldedIntegral
      rw [integral_prod_symm _ hInt]
      congr 1
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      change (∫ q, realEqualIntegrand U (fun x => V (x * z)) Φ₂ s q *
        realAdjacentMatrixWeight η Φ₁ s z ∂D.measure) = _
      exact integral_mul_const _ _

end Langlands.Global.RankinSelbergGlobal.RealJacquet
