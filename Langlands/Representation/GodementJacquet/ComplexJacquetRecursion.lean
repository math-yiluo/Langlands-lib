import Langlands.Representation.GodementJacquet.ComplexJacquetUnipotentAverage
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight
import Langlands.Representation.GodementJacquet.ComplexJacquetQuotientReflection

/-! # The quotient kernel and its duality in the complex Jacquet recursion -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient unipotent_det)
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent (reflectionQuotient reflectionQuotient_mk)
open Langlands.Global.RankinSelbergGlobal hiding detPower dualFunction
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => GeneralLinear n ℂ
local notation "H" => GeneralLinear m ℂ
local notation "U" => upperUnipotent m ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "R" => Matrix (Fin m) (Fin n) ℂ
local notation "w₁" => weylLong m ℂ
local notation "w₂" => weylLong n ℂ
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2

/-- The kernel of Jacquet's quotient integral, on a representative `k` of
the left quotient. The paper's right-quotient variable is `k⁻¹`. -/
def complexJacquetRecursionKernel (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : R → ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ) (g : G) (k : H) : ℂ :=
  complexJacquetDetWeight η g sm *
    complexJacquetUnipotentAverage (-a) D.unipotentHaar (fun X => Φ ((k⁻¹).val * X * g.val)) *
      W k * complexJacquetDetWeight η k⁻¹ sn

private theorem unipotentFourierSum_inv (u : U) :
    unipotentFourierSum r u⁻¹ = -unipotentFourierSum r u := by
  simp only [unipotentFourierSum, UpperUnipotent.inv_adjacent_entry, Finset.sum_neg_distrib]

theorem complexJacquetRecursionKernel_invariant (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : R → ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ)
    (hW : ∀ (u : U) (k : H), W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (g : G) (u : U) (k : H) :
    complexJacquetRecursionKernel a D Φ W η g (u.val * k) =
      complexJacquetRecursionKernel a D Φ W η g k := by
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let f := fun X : R => Φ ((k⁻¹).val * X * g.val)
  have htest : (fun X : R => Φ (((u.val * k)⁻¹).val * X * g.val)) =
      fun X => f ((u⁻¹).val.val * X) := by
    funext X
    simp only [f, mul_inv_rev, Units.val_mul, ← Subgroup.coe_inv, Matrix.mul_assoc]
  have hdet : determinant u.val = 1 := Units.ext (unipotent_det u)
  have hd : determinant (u.val * k)⁻¹ = determinant k⁻¹ := by
    rw [map_inv, map_mul, hdet, one_mul, map_inv]
  have hval : ((u.val * k)⁻¹).val.det = (k⁻¹).val.det :=
    congrArg Units.val hd
  have hw : complexJacquetDetWeight η (u.val * k)⁻¹ sn =
      complexJacquetDetWeight η k⁻¹ sn := by
    rw [complexJacquetDetWeight, complexJacquetDetWeight, hd, detPower, detPower, hval]
  have hphase : traceCharacter a (-unipotentFourierSum r u) *
      traceCharacter a (unipotentFourierSum r u) = 1 := by
    rw [← traceCharacter_add, neg_add_cancel, traceCharacter_zero]
  rw [complexJacquetRecursionKernel, complexJacquetRecursionKernel, htest,
    complexJacquetUnipotentAverage_unipotent, traceCharacter_neg_scale, unipotentFourierSum_inv,
    neg_neg, hW, hw]
  change _ = complexJacquetDetWeight η g sm * complexJacquetUnipotentAverage (-a) D.unipotentHaar f *
    W k * complexJacquetDetWeight η k⁻¹ sn
  calc
    _ = (traceCharacter a (-unipotentFourierSum r u) * traceCharacter a (unipotentFourierSum r u)) *
        (complexJacquetDetWeight η g sm * complexJacquetUnipotentAverage (-a) D.unipotentHaar f *
          W k * complexJacquetDetWeight η k⁻¹ sn) := by ring
    _ = _ := by rw [hphase, one_mul]

/-- Jacquet's iterated quotient integral with its two Haar choices supplied
by the compatible quotient measure data. -/
def complexJacquetRecursion (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : R → ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ) (g : G) : ℂ :=
  ∫ q : Q, complexJacquetRecursionKernel a D Φ W η g q.out ∂D.measure

private theorem largeJacquetDetWeight (η : ℂˣ →* ℂˣ) (g : G) :
    complexJacquetDetWeight η (weylInverseTranspose n ℂ g) sm *
      detPower complexNormalizedAbs g ((m : ℕ) : ℂ) =
      ((η (determinant w₂) : ℂˣ) : ℂ) *
        complexJacquetDetWeight (η.comp invMonoidHom) g sm := by
  -- Fourier integration over the rectangle contributes one factor per row.
  have he : -sm + ((m : ℕ) : ℂ) = sm := by ring
  rw [weylInverseTranspose_apply, complexJacquetDetWeight_mul,
    complexJacquetDetWeight_weylLong, complexJacquetDetWeight_inverseTranspose, mul_assoc,
    ← complexJacquetDetWeight_add]
  rw [he]

private theorem smallJacquetDetWeight (η : ℂˣ →* ℂˣ) (k : H) :
    complexJacquetDetWeight η k⁻¹ sn * detPower complexNormalizedAbs k ((n : ℕ) : ℂ) =
      ((η (determinant w₁) : ℂˣ) : ℂ) *
        complexJacquetDetWeight (η.comp invMonoidHom) (weylInverseTranspose m ℂ k)⁻¹ sn := by
  have he : sn + -((n : ℕ) : ℂ) = -sn := by ring
  have hdet : detPower complexNormalizedAbs k ((n : ℕ) : ℂ) = detPower complexNormalizedAbs k⁻¹ (-((n : ℕ) : ℂ)) := by
    rw [detPower_complex_inv, neg_neg]
  have hk : inverseTranspose m ℂ (weylInverseTranspose m ℂ k)⁻¹ * w₁ = k⁻¹ := by
    simp only [weylInverseTranspose_apply, mul_inv_rev, weylLong_inv, map_mul, ← map_inv,
      inverseTranspose_involutive, inverseTranspose_weylLong, mul_assoc, weylLong_mul_self, mul_one]
  rw [hdet, ← complexJacquetDetWeight_add, he, ← hk,
    complexJacquetDetWeight_mul, complexJacquetDetWeight_inverseTranspose,
    neg_neg, complexJacquetDetWeight_weylLong, mul_comm]

private theorem complexJacquetRecursionKernel_dual (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : SchwartzMap R ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ) (g : G) (k : H) :
    complexJacquetRecursionKernel a D Φ W η (weylInverseTranspose n ℂ g) k =
      ((η (-1) : ℂˣ) : ℂ) ^ m *
        complexJacquetRecursionKernel (-a) D (complexRectangularFourier (-a) Φ)
          (Whittaker.dualFunction r W) (η.comp invMonoidHom) g (weylInverseTranspose m ℂ k) := by
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let gDual := weylInverseTranspose n ℂ g
  let kDual := weylInverseTranspose m ℂ k
  let f := complexRectangularTranslate k⁻¹ (inverseTranspose n ℂ g) Φ
  let F := fun X : R => complexRectangularFourier (-a) Φ ((kDual⁻¹).val * X * g.val)
  have hf (X : R) : f (X * (w₂).val) = Φ ((k⁻¹).val * X * gDual.val) := by
    simp only [f, complexRectangularTranslate_apply, gDual, weylInverseTranspose_apply, Units.val_mul,
      Matrix.mul_assoc]
  have hk : kDual⁻¹ = inverseTranspose m ℂ k⁻¹ * w₁ := by
    simp only [kDual, weylInverseTranspose_apply, mul_inv_rev, weylLong_inv, map_inv]
  have hF (X : R) :
      complexRectangularFourier (-a) f ((w₁).val * X) =
        (detPower complexNormalizedAbs k ((n : ℕ) : ℂ) * detPower complexNormalizedAbs g ((m : ℕ) : ℂ)) * F X := by
    dsimp only [f]
    rw [complexRectangularFourier_translate, complexRectangularJacobian_jacquet,
      inverseTranspose_involutive]
    simp only [F, hk, Units.val_mul, Matrix.mul_assoc]
  have hA := complexJacquetUnipotentAverage_weyl a D.unipotentHaar f
  simp only [hf, hF, complexJacquetUnipotentAverage_const_mul] at hA
  have hW : Whittaker.dualFunction r W kDual = W k := by
    change W (weylInverseTranspose m ℂ kDual) = W k
    rw [show weylInverseTranspose m ℂ kDual = k from weylInverseTranspose_involutive _ _ k]
  have hsign : ((η (determinant w₂) : ℂˣ) : ℂ) * ((η (determinant w₁) : ℂˣ) : ℂ) =
      ((η (-1) : ℂˣ) : ℂ) ^ m := by
    rw [← Units.val_mul, ← map_mul, determinant_weylLong_adjacent, map_pow, Units.val_pow_eq_pow_val]
  unfold complexJacquetRecursionKernel
  change complexJacquetDetWeight η gDual sm * _ * W k * complexJacquetDetWeight η k⁻¹ sn =
    ((η (-1) : ℂˣ) : ℂ) ^ m *
      (complexJacquetDetWeight (η.comp invMonoidHom) g sm * _ *
        Whittaker.dualFunction r W kDual * complexJacquetDetWeight (η.comp invMonoidHom) kDual⁻¹ sn)
  rw [neg_neg, hA, hW]
  change _ = ((η (-1) : ℂˣ) : ℂ) ^ m *
    (complexJacquetDetWeight (η.comp invMonoidHom) g sm *
      complexJacquetUnipotentAverage a D.unipotentHaar F * W k *
        complexJacquetDetWeight (η.comp invMonoidHom) kDual⁻¹ sn)
  calc
    _ = (complexJacquetDetWeight η gDual sm * detPower complexNormalizedAbs g ((m : ℕ) : ℂ)) *
        (complexJacquetDetWeight η k⁻¹ sn * detPower complexNormalizedAbs k ((n : ℕ) : ℂ)) *
          complexJacquetUnipotentAverage a D.unipotentHaar F * W k := by ring
    _ = _ := by
      rw [show complexJacquetDetWeight η gDual sm * detPower complexNormalizedAbs g ((m : ℕ) : ℂ) = _ from
        largeJacquetDetWeight η g,
        show complexJacquetDetWeight η k⁻¹ sn * detPower complexNormalizedAbs k ((n : ℕ) : ℂ) = _ from
          smallJacquetDetWeight η k, ← hsign]
      ring

/-- Duality for the quotient integral of Jacquet's recursion. -/
theorem complexJacquetRecursion_dual (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : SchwartzMap R ℂ) (W : H → ℂ) (η : ℂˣ →* ℂˣ)
    (hW : ∀ (u : U) (k : H), W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (g : G) :
    complexJacquetRecursion a D Φ W η (weylInverseTranspose n ℂ g) =
      ((η (-1) : ℂˣ) : ℂ) ^ m *
        complexJacquetRecursion (-a) D (complexRectangularFourier (-a) Φ)
          (Whittaker.dualFunction r W) (η.comp invMonoidHom) g := by
  let WDual := Whittaker.dualFunction r W
  have hWDual (u : U) (k : H) :
      WDual (u.val * k) = traceCharacter (-a) (unipotentFourierSum r u) * WDual k := by
    change W (weylInverseTranspose m ℂ (u.val * k)) = _
    rw [Whittaker.weylInverseTranspose_left_unipotent, hW, traceCharacter_neg_scale]
    rw [show unipotentFourierSum r (Whittaker.reflectedUnipotent u) = -unipotentFourierSum r u
      from Whittaker.reflectedUnipotent_sum u]
    rfl
  let f := complexJacquetRecursionKernel (-a) D (complexRectangularFourier (-a) Φ)
    WDual (η.comp invMonoidHom) g
  let fQ := descend U f (complexJacquetRecursionKernel_invariant _ _ _ _ _ hWDual g)
  have hfQ (q : Q) : fQ q = f q.out := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  unfold complexJacquetRecursion
  change (∫ q : Q, complexJacquetRecursionKernel a D Φ W η (weylInverseTranspose n ℂ g) q.out
    ∂D.measure) = ((η (-1) : ℂˣ) : ℂ) ^ m * ∫ q : Q, f q.out ∂D.measure
  simp_rw [← hfQ]
  rw [← (measurePreserving_complexReflectionQuotient D).integral_comp
    (reflectionQuotient (K := ℂ) r).measurableEmbedding fQ, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have hreflect : reflectionQuotient (K := ℂ) r q =
      Quotient.mk _ (weylInverseTranspose m ℂ q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    exact reflectionQuotient_mk r q.out
  dsimp only
  rw [hreflect]
  exact complexJacquetRecursionKernel_dual a D Φ W η g q.out

end Langlands.GodementJacquet
