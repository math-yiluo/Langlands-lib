import Langlands.Global.RankinSelberg.ComplexLocalAdjacentIntegrals
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.Global.RankinSelberg.UnfoldingSteps
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear

/-! # Quotient change of variables in the complex adjacent-rank integral -/

noncomputable section

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "gap" => Nat.lt_succ_self r
local notation "G" => Langlands.GeneralLinear (r + 2) ℂ
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rows" => Fin (r + 1) → ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance adjacentMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℂ))
local instance adjacentMatrixOppositeSecondCountable : SecondCountableTopology Matᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
local instance adjacentGLSecondCountable : SecondCountableTopology H :=
  Units.isInducing_embedProduct.secondCountableTopology
local instance adjacentMatrixLocallyCompact : LocallyCompactSpace Mat :=
  inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℂ))
local instance adjacentQuotientSigmaCompact : SigmaCompactSpace Q := by
  have hq := leftQuotient_isOpenQuotientMap N
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

private theorem complexGroupHaar_invInvariant (D : ComplexQuotientMeasureData r) :
    D.groupHaar.IsInvInvariant := by
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.Regular := inferInstance
  have hscalar (a : ℂˣ) :
      Measure.modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a) = 1 := by
    change Measure.modularCharacterFun _ = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ]
    have hcomm : (fun g : H => g * GeneralLinear.scalar a) =
        (fun g : H => GeneralLinear.scalar a * g) :=
      funext fun g => (Matrix.GeneralLinearGroup.scalar_commute a g).symm
    have hmap : Measure.map (fun g : H => g * GeneralLinear.scalar a) μ = μ := by
      rw [hcomm, map_mul_left_eq_self]
    have hf (ν : Measure H) [ν.IsHaarMeasure] (hν : ν = μ) :
        Measure.haarScalarFactor ν μ = 1 := by
      subst ν
      exact Measure.haarScalarFactor_self _
    exact hf _ hmap
  have : T1Space Mat := inferInstanceAs (T1Space (Fin (r + 1) → Fin (r + 1) → ℂ))
  have hmod (g : H) : Measure.modularCharacterFun g = 1 :=
    RankinSelberg.GeneralLinearUnimodularity.character_eq_one Measure.modularCharacter hscalar g
  let : μ.IsMulRightInvariant := ⟨fun g => by
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul, hmod, one_smul]⟩
  exact Unfolding.isInvInvariant_of_isMulRightInvariant μ

private theorem detPower_mul (g k : H) (s : ℂ) : P (g * k) s = P g s * P k s := by
  have hne (x : H) : ‖x.val.det‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (GeneralLinear.determinant x).ne_zero)
  simp only [ArchimedeanLocal.detPower, complexNormalizedAbs, Units.val_mul, Matrix.det_mul,
    norm_mul, mul_pow]
  rw [Real.log_mul (hne g) (hne k), Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem detPower_add (g : H) (s t : ℂ) : P g (s + t) = P g s * P g t := by
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

private def detCharacter (η : ℂˣ →* ℂˣ) (g : H) : ℂ :=
  (η (GeneralLinear.determinant g) : ℂ)

private theorem detCharacter_mul (η : ℂˣ →* ℂˣ) (g k : H) :
    detCharacter η (g * k) = detCharacter η g * detCharacter η k := by
  simp only [detCharacter, map_mul, Units.val_mul]

/-- The smaller-group kernel for the restriction of a recursive Whittaker function
to the padded subgroup, after taking the last-column Fourier transform. -/
def complexAdjacentRestrictionKernel (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U : H → ℂ) (g k : H) : ℂ :=
  detCharacter η g * P g (((r + 1 : ℕ) : ℂ) / 2) *
    Φ₁ (k⁻¹ * g).val * Φ₂ (RankinSelberg.lastRow k) * U k * detCharacter η k⁻¹ * P k⁻¹ ((r : ℂ) / 2)

/-- The square matrix test with the determinant twist and the corank-one shift. -/
def complexAdjacentMatrixWeight (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (s : ℂ) (z : H) : ℂ :=
  Φ₁ z.val * detCharacter η z * P z (s + (r : ℂ) / 2)

/-- The joint quotient and matrix kernel after the change of variables in (8.3). -/
def complexAdjacentUnfoldedKernel (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U V : H → ℂ) (s : ℂ) (p : Q × H) : ℂ :=
  complexEqualIntegrand U (fun x => V (x * p.2)) Φ₂ s p.1 * complexAdjacentMatrixWeight η Φ₁ s p.2

/-- The unfolded matrix integral of smaller equal-rank integrals. -/
def complexAdjacentUnfoldedIntegral (D : ComplexQuotientMeasureData r) (η : ℂˣ →* ℂˣ)
    (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ) (U V : H → ℂ) (s : ℂ) : ℂ :=
  ∫ z : H, complexEqualIntegral D U (fun x => V (x * z)) Φ₂ s *
    complexAdjacentMatrixWeight η Φ₁ s z ∂D.groupHaar

private theorem restrictionKernel_change (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U V : H → ℂ)
    (hUV : ∀ (z : H) (u : N) (g : H), U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z))
    (s : ℂ) (q : Q) (z : H) :
    complexAdjacentRestrictionKernel η Φ₁ Φ₂ U q.out (q.out * z⁻¹) *
      V q.out * P q.out (s - 1 / 2) =
    complexAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s ((rightQuotientShear N).symm (q, z)) := by
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
        rw [← detPower_mul, hkg, ← detPower_mul, hk]
      _ = _ := by rw [detPower_add]; ring
  unfold complexAdjacentUnfoldedKernel
  change _ = complexEqualIntegrand U (fun x => V (x * z)) Φ₂ s
        ((rightQuotientShear N).symm (q, z)).1 *
    (Φ₁ z.val * detCharacter η z * P z (s + (r : ℂ) / 2))
  rw [hq, ComplexCharacterChange.complexEqualIntegrand_mk (hUV z), hk]
  change detCharacter η g * P g (((r + 1 : ℕ) : ℂ) / 2) *
      Φ₁ (k⁻¹ * g).val * Φ₂ (RankinSelberg.lastRow k) * U k * detCharacter η k⁻¹ * P k⁻¹ ((r : ℂ) / 2) *
      V g * P g (s - 1 / 2) = _
  rw [hkg]
  calc
    _ = U k * V g * Φ₂ (RankinSelberg.lastRow k) * Φ₁ z.val *
          (detCharacter η g * detCharacter η k⁻¹) *
          (P g (((r + 1 : ℕ) : ℂ) / 2) * P k⁻¹ ((r : ℂ) / 2) * P g (s - 1 / 2)) := by
      ring
    _ = _ := by rw [hχ, hP]; ring

/-- Jacquet's corank-one change of variables takes the restricted recursion
to a family of smaller equal-rank integrals weighted by a matrix test. -/
theorem complexUnequalIntegral_eq_adjacentUnfolding
    (D : ComplexQuotientMeasureData r) (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (W : G → ℂ) (U V : H → ℂ)
    (hUV : ∀ (z : H) (u : N) (g : H), U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z))
    (hW : ∀ g : H, W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      ∫ k, complexAdjacentRestrictionKernel η Φ₁ Φ₂ U g k ∂D.groupHaar)
    (s : ℂ)
    (hInt : Integrable (complexAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s)
      (D.measure.prod D.groupHaar)) :
    complexUnequalIntegral gap D W V s = complexAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.groupHaar.IsInvInvariant := complexGroupHaar_invInvariant D
  let : D.measure.Regular := D.compatible.regular
  let F := complexAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s
  let e := (rightQuotientShear N).symm
  have he : MeasurePreserving e (D.measure.prod D.groupHaar) (D.measure.prod D.groupHaar) :=
    measurePreserving_rightQuotientShear_symm N D.measure D.groupHaar D.compatible.right_invariant
  have hBefore : Integrable (fun p => F (e p)) (D.measure.prod D.groupHaar) :=
    (he.integrable_comp_emb e.toMeasurableEquiv.measurableEmbedding).mpr hInt
  calc
    complexUnequalIntegral gap D W V s =
        ∫ q : Q, ∫ z : H, F (e (q, z)) ∂D.groupHaar ∂D.measure := by
      change (∫ q, complexUnequalIntegrand gap W V s q ∂D.measure) = _
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      have hshift : (r + 1 - r : ℕ) = 1 := by omega
      simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hshift,
        Nat.cast_one, hW, ← integral_mul_const]
      let g := q.out
      let e₁ := (Homeomorph.inv H).trans (Homeomorph.mulLeft g)
      have he₁ : MeasurePreserving e₁ D.groupHaar D.groupHaar :=
        Measure.measurePreserving_div_left D.groupHaar g
      rw [← he₁.integral_comp e₁.toMeasurableEquiv.measurableEmbedding]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
        restrictionKernel_change η Φ₁ Φ₂ U V hUV s q z)
    _ = ∫ p, F (e p) ∂D.measure.prod D.groupHaar := (integral_prod _ hBefore).symm
    _ = ∫ p, F p ∂D.measure.prod D.groupHaar :=
      he.integral_comp e.toMeasurableEquiv.measurableEmbedding F
    _ = complexAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s := by
      unfold complexAdjacentUnfoldedIntegral
      rw [integral_prod_symm _ hInt]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      change (∫ q, complexEqualIntegrand U (fun x => V (x * z)) Φ₂ s q *
        complexAdjacentMatrixWeight η Φ₁ s z ∂D.measure) = _
      exact integral_mul_const _ _

local notation "J" => (GeneralLinear.scalar (-1 : ℂˣ) : H)
local notation "Dlarge" => ArchimedeanLocal.dualFunction (r + 2)
local notation "Dsmall" => ArchimedeanLocal.dualFunction (r + 1)

private theorem negScalar_mul_val (z : H) : (J * z).val = -z.val := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one]
  change Matrix.diagonal (fun _ : Fin (r + 1) => -(1 : ℂ)) * z.val = -z.val
  rw [← Matrix.diagonal_neg (fun _ : Fin (r + 1) => (1 : ℂ)), Matrix.diagonal_one, neg_mul, one_mul]

private theorem det_negScalar : GeneralLinear.determinant J = (-1 : ℂˣ) ^ (r + 1) := by
  rw [GeneralLinear.determinant, GeneralLinear.scalar, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin]

private theorem detPower_negScalar (s : ℂ) : P J s = 1 := by
  unfold ArchimedeanLocal.detPower
  change Complex.exp (s * (Real.log (complexNormalizedAbs
    (GeneralLinear.determinant J : ℂ)) : ℂ)) = 1
  simp [complexNormalizedAbs, norm_pow]

private theorem sign_square (η : ℂˣ →* ℂˣ) : ((η (-1) : ℂ) ^ (r + 1)) ^ 2 = 1 := by
  have hη : (η (-1) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    simp [pow_two]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hη, one_pow]

/-- Reversing the sign of the square matrix Fourier test contributes the determinant
sign and the central sign of the right-translated Whittaker function. -/
theorem complexAdjacentUnfoldedIntegral_reflect (D : ComplexQuotientMeasureData r)
    (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (U V : H → ℂ) (c : ℂ) (hV : ∀ g, V (g * J) = c * V g) (s : ℂ) :
    (η (-1) : ℂ) ^ (r + 1) *
      complexAdjacentUnfoldedIntegral D η (fun X => Φ₁ (-X)) Φ₂ U V s =
      c * complexAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let F := fun z : H => complexEqualIntegral D U (fun x => V (x * z)) Φ₂ s *
    complexAdjacentMatrixWeight η (fun X => Φ₁ (-X)) s z
  have hΦ (z : H) : complexAdjacentMatrixWeight η (fun X => Φ₁ (-X)) s (J * z) =
      (η (-1) : ℂ) ^ (r + 1) * complexAdjacentMatrixWeight η Φ₁ s z := by
    unfold complexAdjacentMatrixWeight
    simp only [negScalar_mul_val, neg_neg, detCharacter_mul, detPower_mul, detPower_negScalar, one_mul]
    simp only [detCharacter, det_negScalar, map_pow, Units.val_pow_eq_pow_val]
    ring
  have hEq (z : H) : complexEqualIntegral D U (fun x => V (x * (J * z))) Φ₂ s =
      c * complexEqualIntegral D U (fun x => V (x * z)) Φ₂ s := by
    have hV' (x : H) : V (x * (J * z)) = c * V (x * z) := by
      rw [Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, hV]
    change (∫ q, complexEqualIntegrand U (fun x => V (x * (J * z))) Φ₂ s q ∂D.measure) =
      c * ∫ q, complexEqualIntegrand U (fun x => V (x * z)) Φ₂ s q ∂D.measure
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, hV']
    ring
  have hF (z : H) : F (J * z) = ((η (-1) : ℂ) ^ (r + 1) * c) *
      (complexEqualIntegral D U (fun x => V (x * z)) Φ₂ s * complexAdjacentMatrixWeight η Φ₁ s z) := by
    dsimp only [F]
    rw [hEq, hΦ]
    ring
  change (η (-1) : ℂ) ^ (r + 1) * (∫ z, F z ∂D.groupHaar) = _
  rw [← integral_mul_left_eq_self F J]
  simp_rw [hF, integral_const_mul]
  change _ = c * ∫ z, complexEqualIntegral D U (fun x => V (x * z)) Φ₂ s *
    complexAdjacentMatrixWeight η Φ₁ s z ∂D.groupHaar
  rw [← mul_assoc, ← mul_assoc, ← pow_two, sign_square, one_mul]

private theorem complexUnequalIntegral_eq_scaled_adjacentUnfolding (D : ComplexQuotientMeasureData r)
    (η : ℂˣ →* ℂˣ) (Φ₁ : Mat → ℂ) (Φ₂ : Rows → ℂ)
    (W : G → ℂ) (U V : H → ℂ)
    (hUV : ∀ (z : H) (u : N) (g : H), U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z))
    (b : ℂ) (hb : b ≠ 0)
    (hW : ∀ g : H, W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      b * ∫ k, complexAdjacentRestrictionKernel η Φ₁ Φ₂ U g k ∂D.groupHaar)
    (s : ℂ)
    (hInt : Integrable (complexAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s)
      (D.measure.prod D.groupHaar)) :
    complexUnequalIntegral gap D W V s =
      b * complexAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s := by
  let W₁ := fun g => b⁻¹ * W g
  have hW₁ (g : H) : W₁ (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      ∫ k, complexAdjacentRestrictionKernel η Φ₁ Φ₂ U g k ∂D.groupHaar := by
    simp only [W₁, hW, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
  have h := complexUnequalIntegral_eq_adjacentUnfolding D η Φ₁ Φ₂ W₁ U V hUV hW₁ s hInt
  have hscale : complexUnequalIntegral gap D W₁ V s = b⁻¹ * complexUnequalIntegral gap D W V s := by
    change (∫ q, complexUnequalIntegrand gap W₁ V s q ∂D.measure) =
      b⁻¹ * (∫ q, complexUnequalIntegrand gap W V s q ∂D.measure)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [W₁, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, mul_assoc]
  rw [hscale] at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]

variable (r) in
/-- The paired corank-one unfolding with positive square Fourier sign, given the
restricted primal and dual recursion formulas and absolute convergence of the joint kernels. -/
def ComplexLocalAdjacentUnfoldingStatement : Prop :=
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (η : ℂˣ →* ℂˣ)
    (Φ₁ Φ₁d : Mat → ℂ) (Φ₂ Φ₂d : Rows → ℂ) (W : G → ℂ) (U V : H → ℂ) (c : ℂ),
    (∀ (z : H) (u : N) (g : H), U (u.val * g) * V ((u.val * g) * z) = U g * V (g * z)) →
    (∀ (z : H) (u : N) (g : H),
      Dsmall U (u.val * g) * Dsmall V ((u.val * g) * z) = Dsmall U g * Dsmall V (g * z)) →
    (∀ g, Dsmall V (g * J) = c * Dsmall V g) →
    (∀ g : H, W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      ∫ k, complexAdjacentRestrictionKernel η Φ₁ Φ₂ U g k ∂D.groupHaar) →
    (∀ g : H, Dlarge W (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
      (η (-1) : ℂ) ^ (r + 1) *
        ∫ k, complexAdjacentRestrictionKernel (η.comp invMonoidHom) (fun X => Φ₁d (-X))
          Φ₂d (Dsmall U) g k ∂D.groupHaar) →
    ∀ s : ℂ, Integrable (complexAdjacentUnfoldedKernel η Φ₁ Φ₂ U V s)
        (D.measure.prod D.groupHaar) →
      Integrable (complexAdjacentUnfoldedKernel (η.comp invMonoidHom) (fun X => Φ₁d (-X))
        Φ₂d (Dsmall U) (Dsmall V) s) (D.measure.prod D.groupHaar) →
      complexUnequalIntegral gap D W V s = complexAdjacentUnfoldedIntegral D η Φ₁ Φ₂ U V s ∧
      complexUnequalDualIntegral gap a D W V s =
        c * complexAdjacentUnfoldedIntegral D (η.comp invMonoidHom) Φ₁d Φ₂d (Dsmall U) (Dsmall V) s

theorem complexLocalAdjacentUnfolding : ComplexLocalAdjacentUnfoldingStatement r := by
  intro a D η Φ₁ Φ₁d Φ₂ Φ₂d W U V c hUV hUVd hV hW hWd s hInt hIntd
  have hη : (η (-1) : ℂ) ^ (r + 1) ≠ 0 := pow_ne_zero _ (η (-1)).ne_zero
  have hsign : ((η.comp invMonoidHom) (-1) : ℂ) ^ (r + 1) = (η (-1) : ℂ) ^ (r + 1) := by
    change (η ((-1 : ℂˣ)⁻¹) : ℂ) ^ (r + 1) = _
    simp
  refine ⟨complexUnequalIntegral_eq_adjacentUnfolding D η Φ₁ Φ₂ W U V hUV hW s hInt, ?_⟩
  calc
    complexUnequalDualIntegral gap a D W V s =
        complexUnequalIntegral gap D (Dlarge W) (Dsmall V) s :=
      complexUnequalDualIntegral_adjacent a D W V s
    _ = (η (-1) : ℂ) ^ (r + 1) *
        complexAdjacentUnfoldedIntegral D (η.comp invMonoidHom) (fun X => Φ₁d (-X))
          Φ₂d (Dsmall U) (Dsmall V) s :=
      complexUnequalIntegral_eq_scaled_adjacentUnfolding D (η.comp invMonoidHom) _ Φ₂d
        (Dlarge W) (Dsmall U) (Dsmall V) hUVd _ hη hWd s hIntd
    _ = c * complexAdjacentUnfoldedIntegral D (η.comp invMonoidHom) Φ₁d Φ₂d
        (Dsmall U) (Dsmall V) s := by
      rw [← hsign]
      exact complexAdjacentUnfoldedIntegral_reflect D (η.comp invMonoidHom) Φ₁d Φ₂d
        (Dsmall U) (Dsmall V) c hV s

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
