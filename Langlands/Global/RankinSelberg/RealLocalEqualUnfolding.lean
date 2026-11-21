import Langlands.Global.RankinSelberg.RealGodementColumnQuotient
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints
import Langlands.Global.RankinSelberg.RealEqualConvergence

/-! # Unfolding the real equal-rank integral of a Godement recursion -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Langlands.Whittaker
open Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow lastRow_unipotent_mul unipotent_det)
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "n" => (t + 2)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "U" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ
local notation "Q'" => LeftUnipotentQuotient (t + 1) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "pad" => (padGL (R := ℝ) (Nat.le_succ (t + 1)))
local notation "P" => (ArchimedeanLocal.detPower (K := ℝ) realNormalizedAbs)

/-- Take the first `t+1` rows of a square of size `t+2`. -/
def squareFirstRows (A : Y) : X := A.submatrix Fin.castSucc id

/-- The square matrix test in (8.1), with the last-row test as the second factor. -/
def equalSquareTest (Φ : X → ℂ) (φ : (Fin n → ℝ) → ℂ) (A : Y) : ℂ :=
  Φ (squareFirstRows A) * φ (A (Fin.last m))

private theorem squareFirstRows_pad_mul (h : G) (g : H) :
    squareFirstRows (pad h * g).val = h.val * squareFirstRows g.val := by
  ext i j
  change ∑ k, (pad h).val i.castSucc k * g.val k j = ∑ k, h.val i k * g.val k.castSucc j
  rw [Fin.sum_univ_castSucc, UnequalAnalytic.padGL_col _ _ _ (by simp),
    Matrix.one_apply_ne (ne_of_lt i.castSucc_lt_last), zero_mul, add_zero]
  congr 1
  funext k
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨i.isLt, k.isLt⟩]
  rfl

private theorem lastRow_pad_mul (h : G) (g : H) : lastRow (pad h * g) = lastRow g := by
  funext j
  change ∑ k, (pad h).val (Fin.last m) k * g.val k j = g.val (Fin.last m) j
  simp_rw [UnequalAnalytic.padGL_row _ _ _ (by simp : m ≤ (Fin.last m).val)]
  exact congrArg (fun A : Y => A (Fin.last m) j) (Matrix.one_mul g.val)

private theorem stepRectangle_mul_weyl (z : StepCoordinates m → ℝ) (g : H) :
    (weylLong m ℝ).val * (stepRectangle z * (weylLong n ℝ * g).val) =
      squareFirstRows ((upperStepChart m z).val * g).val := by
  let u := (upperStepChart m z).val
  have hre : stepRectangle z = (u * weylLong n ℝ).val.submatrix
      (fun i : Fin m => i.rev.castSucc) id := by
    ext i j
    rw [stepRectangle_eq_upperStepChart, Matrix.submatrix_apply, mul_weylLong_entry, Fin.rev_succ]
    rfl
  rw [hre]
  change (weylLong m ℝ).val * ((u * weylLong n ℝ).val.submatrix
    (fun i : Fin m => i.rev.castSucc) (Equiv.refl (Fin n)) *
    (weylLong n ℝ * g).val.submatrix (Equiv.refl (Fin n)) id) = _
  rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_assoc u,
    ← mul_assoc (weylLong n ℝ), weylLong_mul_self, one_mul]
  have hw : (weylLong m ℝ).val = (1 : Matrix (Fin m) (Fin m) ℝ).submatrix id Fin.revPerm := by
    ext i j
    simp [weylLong_entry, Matrix.one_apply, eq_comm]
  rw [hw, show (u * g).val.submatrix (fun i : Fin m => i.rev.castSucc) id =
    (squareFirstRows (u * g).val).submatrix Fin.revPerm id from rfl,
    Matrix.submatrix_mul_equiv, Matrix.one_mul]
  rfl

private theorem detPower_eq_cpow {j : ℕ} (g : Langlands.GeneralLinear j ℝ) (s : ℂ) :
    P g s = ((|g.val.det| : ℝ) : ℂ) ^ s := by
  have h : (|(g.val.det)| : ℝ) ≠ 0 := abs_ne_zero.mpr (determinant g).ne_zero
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h), ← Complex.ofReal_log (abs_nonneg _)]
  exact congrArg Complex.exp (mul_comm _ _)

private theorem detPower_inv (g : G) (s : ℂ) : P g⁻¹ s = P g (-s) := by
  simp only [ArchimedeanLocal.detPower, realNormalizedAbs, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv, Units.val_inv_eq_inv_val, abs_inv, Real.log_inv, Complex.ofReal_neg,
    mul_neg, neg_mul]

private theorem determinantWeight_comp_pad (d : RealCharacterData) (s : ℂ) (g : G) :
    determinantWeight d s (pad g) = determinantWeight d s g := by
  unfold determinantWeight
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  congr 1
  exact Units.ext (UnequalAnalytic.det_padGL _ g)

private theorem determinantWeight_add (d : RealCharacterData) {j : ℕ}
    (g : Langlands.GeneralLinear j ℝ) (s z : ℂ) :
    determinantWeight d s g * P g z = determinantWeight d (s + z) g := by
  rw [detPower_eq_cpow]
  change ((d.character (determinant g) : ℂ) * ((|g.val.det| : ℝ) : ℂ) ^ s) * _ =
    (d.character (determinant g) : ℂ) * ((|g.val.det| : ℝ) : ℂ) ^ (s + z)
  have h : (|(g.val.det)| : ℝ) ≠ 0 := abs_ne_zero.mpr (determinant g).ne_zero
  rw [mul_assoc, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr h)]

private theorem determinantWeight_unip_mul (d : RealCharacterData) (s : ℂ) (u : U) (g : H) :
    determinantWeight d s (u.val * g) = determinantWeight d s g := by
  have hu : determinant u.val = 1 := Units.ext (unipotent_det u)
  have h : determinant (u.val * g) = determinant g := by
    rw [map_mul, hu, one_mul]
  simp only [determinantWeight, MonoidHom.comp_apply, h]

private theorem determinantWeight_weyl (d : RealCharacterData) (j : ℕ) (s : ℂ) :
    determinantWeight d s (weylLong j ℝ) = (d.character (determinant (weylLong j ℝ)) : ℂ) := by
  have habs : |(weylLong j ℝ).val.det| = 1 := by
    apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
    rw [pow_two, ← abs_mul, ← Matrix.det_mul, ← Units.val_mul, weylLong_mul_self,
      Units.val_one, Matrix.det_one, abs_one]
  change (d.character (determinant (weylLong j ℝ)) : ℂ) * ((|(weylLong j ℝ).val.det| : ℝ) : ℂ) ^ s = _
  rw [habs, Complex.ofReal_one, Complex.one_cpow, mul_one]

local notation "C(" d ")" => ((RealCharacterData.character d (-1) : ℂ) ^ (t + 1))

private theorem determinantWeight_weyl_pair (d : RealCharacterData) :
    determinantWeight d ((m : ℂ) / 2) (weylLong n ℝ) *
      determinantWeight d ((n : ℂ) / 2) (weylLong m ℝ) = C(d) := by
  rw [determinantWeight_weyl, determinantWeight_weyl, ← Units.val_mul, ← map_mul]
  rw [Langlands.RankinSelberg.RankOneGammaTwist.determinant_weylLong_succ, mul_assoc,
    ← map_mul, weylLong_mul_self, map_one, mul_one, map_pow, Units.val_pow_eq_pow_val]

/-- The Godement quotient coefficient evaluated at `w_n g`, with the two
constant Weyl determinants absorbed into its normalization. -/
def equalRecursiveCoefficient (b : ℝˣ) (D : RealQuotientMeasureData t) (Φ : 𝓢(X, ℂ))
    (W : G → ℂ) (hW : KernelWhittakerLaw b W) (d : RealCharacterData) (g : H) : ℂ :=
  C(d) * ∫ q, quotientKernel b Φ W hW d (weylLong n ℝ * g) q ∂D.measure

/-- The joint integrand in (8.1), written using a continuous real quotient section. -/
def equalUnfoldedKernel (d : RealCharacterData) (Ψ : Y → ℂ) (W : G → ℂ) (V : H → ℂ)
    (s : ℂ) (p : Q × H) : ℂ :=
  let h := quotientRepresentative t p.1
  Ψ p.2.val * V (pad h * p.2) * determinantWeight d (s + (m : ℂ) / 2) p.2 *
    W h * P h (s - 1 / 2)

private theorem representative_class (q : Q) : Quotient.mk _ (quotientRepresentative t q) = q := by
  have h := (unipotentQuotientHomeomorph t).left_inv (1, q)
  simpa only [unipotentQuotientHomeomorph, OneMemClass.coe_one, one_mul] using congrArg Prod.snd h

private theorem continuous_representative : Continuous (quotientRepresentative t) := by
  have h : quotientRepresentative t = (unipotentQuotientHomeomorph t) ∘ (fun q : Q => (1, q)) := by
    funext q
    change _ = (1 : G) * quotientRepresentative t q
    exact (one_mul _).symm
  rw [h]
  exact (unipotentQuotientHomeomorph t).continuous.comp (continuous_const.prodMk continuous_id)

private theorem shifted_kernel (b : ℝˣ) (Φ : 𝓢(X, ℂ)) (φ : (Fin n → ℝ) → ℂ)
    (W : G → ℂ) (V : H → ℂ) (hV : KernelWhittakerLaw (-b) V)
    (d : RealCharacterData) (s : ℂ) (q : Q) (g : H) (z : StepCoordinates m → ℝ) :
    let h := quotientRepresentative t q
    let u := upperStepChart m z
    equalUnfoldedKernel d (equalSquareTest Φ φ) W V s (q, (pad h)⁻¹ * (u.val * g)) =
      (C(d) * determinantWeight d ((m : ℂ) / 2) (weylLong n ℝ * g) * W h *
        determinantWeight d ((n : ℂ) / 2) (h⁻¹ * weylLong m ℝ) * V g * φ (lastRow g) * P g s) *
      kernelSliceIntegrand b Φ (h⁻¹ * weylLong m ℝ) (weylLong n ℝ * g) z := by
  dsimp only
  let h := quotientRepresentative t q
  let u := upperStepChart m z
  have hshift : pad h * ((pad h)⁻¹ * (u.val * g)) = u.val * g := by simp
  have hrect : (h⁻¹ * weylLong m ℝ).val * stepRectangle z * (weylLong n ℝ * g).val =
      squareFirstRows (pad h⁻¹ * (u.val * g)).val := by
    rw [squareFirstRows_pad_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      stepRectangle_mul_weyl]
  have hrow : (pad h⁻¹ * (u.val * g)).val (Fin.last m) = lastRow g := by
    change lastRow (pad h⁻¹ * (u.val * g)) = lastRow g
    rw [lastRow_pad_mul, lastRow_unipotent_mul]
  have hphase : (standardCharacter (realScaledCharacter (- -b)) (t + 1) u : ℂ) =
      (realScaledCharacter b).complex (stepPhase z) := by
    rw [neg_neg, stepPhase_eq_upperStepChart]
    rfl
  have hpow : determinantWeight d (s + (m : ℂ) / 2) (pad h⁻¹ * (u.val * g)) *
      P h (s - 1 / 2) = determinantWeight d ((m : ℂ) / 2) g * P g s *
        determinantWeight d ((n : ℂ) / 2) h⁻¹ := by
    have hi : P h (s - 1 / 2) = P h⁻¹ (-(s - 1 / 2)) := by
      rw [detPower_inv, neg_neg]
    have hsplit : determinantWeight d (s + (m : ℂ) / 2) g =
        determinantWeight d ((m : ℂ) / 2) g * P g s := by
      rw [determinantWeight_add, add_comm s ((m : ℂ) / 2)]
    rw [map_mul, determinantWeight_comp_pad, determinantWeight_unip_mul, hsplit, hi]
    calc
      _ = (determinantWeight d ((m : ℂ) / 2) g * P g s) *
          (determinantWeight d (s + (m : ℂ) / 2) h⁻¹ * P h⁻¹ (-(s - 1 / 2))) := by ring
      _ = _ := by
        rw [determinantWeight_add d h⁻¹, show s + (m : ℂ) / 2 + -(s - 1 / 2) =
          (n : ℂ) / 2 by ring]
  have hC : C(d) * C(d) = 1 := by
    rw [← pow_add, ← Nat.two_mul, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow]
    norm_num
  change equalUnfoldedKernel d (equalSquareTest Φ φ) W V s (q, (pad h)⁻¹ * (u.val * g)) = _
  dsimp only [equalUnfoldedKernel, equalSquareTest, kernelSliceIntegrand]
  rw [hshift, ← map_inv pad, hrow, ← hrect, hV u g, hphase]
  calc
    _ = (Φ ((h⁻¹ * weylLong m ℝ).val * stepRectangle z * (weylLong n ℝ * g).val) *
          (realScaledCharacter b).complex (stepPhase z) * V g * φ (lastRow g) * W h) *
        (determinantWeight d (s + (m : ℂ) / 2) (pad h⁻¹ * (u.val * g)) * P h (s - 1 / 2)) := by ring
    _ = _ := by
      rw [hpow, map_mul (determinantWeight d ((m : ℂ) / 2)),
        map_mul (determinantWeight d ((n : ℂ) / 2))]
      have hcoef : C(d) * (determinantWeight d ((m : ℂ) / 2) (weylLong n ℝ) *
          determinantWeight d ((n : ℂ) / 2) (weylLong m ℝ)) = 1 := by
        rw [determinantWeight_weyl_pair, hC]
      linear_combination -hcoef *
        (Φ ((h⁻¹ * weylLong m ℝ).val * stepRectangle z * (weylLong n ℝ * g).val) *
          (realScaledCharacter b).complex (stepPhase z) * V g * φ (lastRow g) * W h *
          determinantWeight d ((m : ℂ) / 2) g * P g s * determinantWeight d ((n : ℂ) / 2) h⁻¹)

set_option maxHeartbeats 600000 in
/-- Orbit averaging the translated matrix kernel recovers the Godement quotient
kernel pointwise, with the exact phase and both determinant shifts. -/
theorem integral_equalUnfoldedKernel_orbit (b : ℝˣ) (Φ : 𝓢(X, ℂ))
    (φ : (Fin n → ℝ) → ℂ) (W : G → ℂ) (hW : KernelWhittakerLaw b W)
    (V : H → ℂ) (hV : KernelWhittakerLaw (-b) V) (d : RealCharacterData) (s : ℂ) (q : Q) (g : H) :
    (∫ u : U, equalUnfoldedKernel d (equalSquareTest Φ φ) W V s
        (q, (pad (quotientRepresentative t q))⁻¹ * (u.val * g)) ∂upperStepHaar (t + 1) b) =
      C(d) * quotientKernel b Φ W hW d (weylLong n ℝ * g) q * V g * φ (lastRow g) * P g s := by
  let h := quotientRepresentative t q
  let E := (upperStepChart m).toMeasurableEquiv
  let f := fun u : U => equalUnfoldedKernel d (equalSquareTest Φ φ) W V s (q, (pad h)⁻¹ * (u.val * g))
  have he : MeasurePreserving E (stepMeasure m b) (upperStepHaar (t + 1) b) :=
    measurePreserving_upperStepChart m b
  have hrep : Quotient.mk (QuotientGroup.rightRel (GeneralLinear.upperUnipotent m ℝ)) h = q :=
    representative_class q
  let w := C(d) * determinantWeight d ((m : ℂ) / 2) (weylLong n ℝ * g) * W h *
      determinantWeight d ((n : ℂ) / 2) (h⁻¹ * weylLong m ℝ) * V g * φ (lastRow g) * P g s
  calc
    _ = ∫ z, f (E z) ∂stepMeasure m b := (he.integral_comp' f).symm
    _ = ∫ z, w * kernelSliceIntegrand b Φ (h⁻¹ * weylLong m ℝ) (weylLong n ℝ * g) z ∂stepMeasure m b :=
      integral_congr_ae (Filter.Eventually.of_forall (shifted_kernel b Φ φ W V hV d s q g))
    _ = w * kernelSlice b Φ (h⁻¹ * weylLong m ℝ) (weylLong n ℝ * g) := integral_const_mul _ _
    _ = _ := by
      conv_rhs => rw [← hrep, quotientKernel_mk]
      simp only [kernelIntegrand, w, Nat.cast_succ]
      rw [add_assoc (t : ℂ) 1 1, show (1 : ℂ) + 1 = 2 by norm_num]
      ac_rfl

private local instance (j : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear (j + 1) ℝ) := by
  let _ : LocallyCompactSpace (Matrix (Fin (j + 1)) (Fin (j + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (j + 1) → Fin (j + 1) → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace

private local instance (j : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (j + 1) ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

private local instance (j : ℕ) : SigmaCompactSpace (LeftUnipotentQuotient j ℝ) := by
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective
    (s := QuotientGroup.rightRel (GeneralLinear.upperUnipotent (j + 1) ℝ)))]
  exact isSigmaCompact_range continuous_quotient_mk'

private local instance (j : ℕ) : SigmaCompactSpace (GeneralLinear.upperUnipotent (j + 1) ℝ) := by
  have h : IsClosed (GeneralLinear.upperUnipotent (j + 1) ℝ : Set (Langlands.GeneralLinear (j + 1) ℝ)) :=
    UpperUnipotent.isClosed
  exact h.isClosedEmbedding_subtypeVal.sigmaCompactSpace

variable (t) in
private def equalUnfoldingShift : Q × H ≃ᵐ Q × H where
  toFun p := (p.1, (pad (quotientRepresentative t p.1))⁻¹ * p.2)
  invFun p := (p.1, pad (quotientRepresentative t p.1) * p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk (((UnequalAnalytic.continuous_padGL _).comp
    (continuous_representative.comp continuous_fst)).inv.mul continuous_snd).measurable
  measurable_invFun := measurable_fst.prodMk (((UnequalAnalytic.continuous_padGL _).comp
    (continuous_representative.comp continuous_fst)).mul continuous_snd).measurable

private theorem measurePreserving_equalUnfoldingShift (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) :
    MeasurePreserving (equalUnfoldingShift t) (D.measure.prod D'.groupHaar)
      (D.measure.prod D'.groupHaar) := by
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.groupHaar_isHaar
  refine (MeasurePreserving.id D.measure).skew_product
    (g := fun q g => (pad (quotientRepresentative t q))⁻¹ * g) ?_ ?_
  · exact measurable_snd.comp (equalUnfoldingShift t).measurable
  · exact Filter.Eventually.of_forall fun q => map_mul_left_eq_self D'.groupHaar
      (pad (quotientRepresentative t q))⁻¹

variable (t) in
private def equalUnfoldingChart : Q' × (Q × U) ≃ᵐ Q × H :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.prodAssoc.trans (
    ((MeasurableEquiv.refl Q).prodCongr (unipotentQuotientHomeomorph (t + 1)).toMeasurableEquiv).trans
    (equalUnfoldingShift t)))

private theorem measurePreserving_equalUnfoldingChart (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) :
    MeasurePreserving (equalUnfoldingChart t) (D'.measure.prod (D.measure.prod D'.unipotentHaar))
      (D.measure.prod D'.groupHaar) := by
  let := D.unipotentHaar_rightInvariant
  let := D'.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.compatible.regular
  let := D'.unipotentHaar_isHaar
  exact (measurePreserving_equalUnfoldingShift D D').comp
    (((MeasurePreserving.id D.measure).prod (measurePreserving_unipotentQuotient D')).comp
      ((measurePreserving_prodAssoc D.measure D'.unipotentHaar D'.measure).comp
        Measure.measurePreserving_swap))

private theorem integral_equalUnfoldingChart_orbit (D' : RealQuotientMeasureData (t + 1))
    (b : ℝˣ) (scale : ℝ≥0) (hμ : D'.unipotentHaar = scale • upperStepHaar (t + 1) b)
    (Φ : 𝓢(X, ℂ)) (φ : (Fin n → ℝ) → ℂ) (W : G → ℂ) (hW : KernelWhittakerLaw b W)
    (V : H → ℂ) (hV : KernelWhittakerLaw (-b) V) (d : RealCharacterData) (s : ℂ) (q : Q) (q' : Q') :
    (∫ u : U, equalUnfoldedKernel d (equalSquareTest Φ φ) W V s
        (equalUnfoldingChart t (q', (q, u))) ∂D'.unipotentHaar) =
      (scale : ℂ) * (C(d) * quotientKernel b Φ W hW d (weylLong n ℝ * q'.out) q * V q'.out *
        φ (lastRow q'.out) * P q'.out s) := by
  let := D'.unipotentHaar_rightInvariant
  let v : U := RealIwasawa.npart q'.out
  have hv : v.val * quotientRepresentative (t + 1) q' = q'.out := by
    have h := (unipotentQuotientHomeomorph (t + 1)).right_inv q'.out
    change v.val * quotientRepresentative (t + 1) (Quotient.mk _ q'.out) = q'.out at h
    rwa [Quotient.out_eq] at h
  let f := fun u : U => equalUnfoldedKernel d (equalSquareTest Φ φ) W V s
    (q, (pad (quotientRepresentative t q))⁻¹ * (u.val * quotientRepresentative (t + 1) q'))
  calc
    _ = ∫ u : U, f (u * v) ∂D'.unipotentHaar := (integral_mul_right_eq_self f v).symm
    _ = ∫ u : U, equalUnfoldedKernel d (equalSquareTest Φ φ) W V s
        (q, (pad (quotientRepresentative t q))⁻¹ * (u.val * q'.out)) ∂D'.unipotentHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by simp only [f, Subgroup.coe_mul, mul_assoc, hv]
    _ = _ := by
      rw [hμ, integral_smul_nnreal_measure]
      change (scale : ℝ) • (_ : ℂ) = _
      rw [Complex.real_smul, integral_equalUnfoldedKernel_orbit b Φ φ W hW V hV d s q q'.out]

variable (t) in
/-- The actual equal-rank integral of a Godement quotient coefficient unfolds to
Jacquet's integral (8.1), assuming joint absolute integrability of the unfolded
kernel. The Haar comparison coefficient is on the equal-integral side. -/
def RealLocalEqualUnfoldingStatement : Prop :=
  ∀ (b : ℝˣ) (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1))
    (scale : ℝ≥0), 0 < scale → D'.unipotentHaar = scale • upperStepHaar (t + 1) b →
  ∀ (Φ : 𝓢(X, ℂ)) (φ : (Fin n → ℝ) → ℂ) (W : G → ℂ) (hW : KernelWhittakerLaw b W)
    (V : H → ℂ) (d : RealCharacterData) (s : ℂ), KernelWhittakerLaw (-b) V →
    Integrable (equalUnfoldedKernel d (equalSquareTest Φ φ) W V s) (D.measure.prod D'.groupHaar) →
    Integrable (equalIntegrand realNormalizedAbs (equalRecursiveCoefficient b D Φ W hW d) V φ s) D'.measure ∧
      (scale : ℂ) * realEqualIntegral D' (equalRecursiveCoefficient b D Φ W hW d) V φ s =
        ∫ p, equalUnfoldedKernel d (equalSquareTest Φ φ) W V s p ∂(D.measure.prod D'.groupHaar)

set_option maxHeartbeats 800000 in
/-- Unfolding on the actual compatible quotient data, by the real Iwasawa Weil formula and Fubini. -/
theorem realLocalEqualUnfolding : RealLocalEqualUnfoldingStatement t := by
  intro b D D' scale hscale hμ Φ φ W hW V d s hV hf
  let := D.unipotentHaar_rightInvariant
  let := D'.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let := D'.compatible.regular
  let := D'.unipotentHaar_isHaar
  let J := equalUnfoldedKernel d (equalSquareTest Φ φ) W V s
  let F := J ∘ equalUnfoldingChart t
  let I := equalIntegrand realNormalizedAbs (equalRecursiveCoefficient b D Φ W hW d) V φ s
  have he := measurePreserving_equalUnfoldingChart D D'
  have hF : Integrable F (D'.measure.prod (D.measure.prod D'.unipotentHaar)) :=
    he.integrable_comp_of_integrable hf
  have hI : (fun q' : Q' => ∫ p, F (q', p) ∂(D.measure.prod D'.unipotentHaar))
      =ᵐ[D'.measure] fun q' : Q' => (scale : ℂ) * I q' := by
    filter_upwards [hF.prod_right_ae] with q' hq'
    rw [integral_prod _ hq']
    simp_rw [show ∀ q : Q, (∫ u : U, F (q', (q, u)) ∂D'.unipotentHaar) = _ from
      fun q => integral_equalUnfoldingChart_orbit D' b scale hμ Φ φ W hW V hV d s q q']
    simp only [integral_const_mul, integral_mul_const, I, equalIntegrand, equalRecursiveCoefficient]
  have hUnit : IsUnit (scale : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hscale.ne')
  refine ⟨(integrable_const_mul_iff hUnit I).mp (hF.integral_prod_left.congr hI), ?_⟩
  change (scale : ℂ) * (∫ q', I q' ∂D'.measure) = ∫ p, J p ∂(D.measure.prod D'.groupHaar)
  calc
    _ = ∫ q', (scale : ℂ) * I q' ∂D'.measure := (integral_const_mul _ _).symm
    _ = ∫ q', ∫ p, F (q', p) ∂(D.measure.prod D'.unipotentHaar) ∂D'.measure := integral_congr_ae hI.symm
    _ = ∫ p, F p ∂(D'.measure.prod (D.measure.prod D'.unipotentHaar)) := (integral_prod _ hF).symm
    _ = _ := he.integral_comp' J

end Langlands.Global.RankinSelbergGlobal.RealGodement
