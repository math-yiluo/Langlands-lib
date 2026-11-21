import Langlands.Automorphic.CuspidalLeviCoefficientSlices
import Langlands.Global.CuspidalLeviCoefficientEvaluation
import Langlands.Global.AdelicBlockPeriodPlaceLie
import Langlands.Global.AdelicBlockPeriodPlaceCompact
import Langlands.Representation.TensorProduct.ProductFunctionSlices

/-! # Lie and compact identities of a restored Levi coefficient tensor -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 120000

universe u

namespace Langlands.Global

open Langlands.Automorphic Langlands.GeneralLinear ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n) (R : ∀ i, OperatorRealization F (B.size i))
  {W : Type u} [AddCommGroup W] [Module ℂ W]

local instance periodEvalRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance periodEvalContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance periodEvalSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance periodEvalFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance periodEvalStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance periodEvalRealizationGroup {d : ℕ} (S' : OperatorRealization F d) :
    AddCommGroup S'.Space := Submodule.addCommGroup _
local instance periodEvalOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "E" => fun i => operatorRealizationFunctionEvaluation (R i)
local notation "P" => translatedBlockLeviRestriction F B S

variable (j : W →ₗ[ℂ] TranslatedBlockConstantTerms F B S)
  (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin B.length), ↥((R i).Space)))

/-- The tensor evaluates to the actual translated period on the Levi. -/
def IsRealizedLeviPeriodCoefficient : Prop :=
  ∀ (w : W) (m : M), functionTensorEvaluation E (ev w) m = P (j w) m

private theorem coefficientEvaluation_injective :
    ∀ i : Fin B.length, Function.Injective (operatorRealizationFunctionEvaluation (R i)) :=
  fun i => operatorRealizationFunctionEvaluation_injective (R i)

private def realizedLeviSlicesOfCoefficient (h : IsRealizedLeviPeriodCoefficient B S R j ev)
    (i : Fin B.length) : RealizedBlockLeviSlices F B S j i (R i) := by
  let slice (m : M) := functionTensorSlice E i (coefficientEvaluation_injective B R i) m
  refine ⟨fun m => (slice m).comp ev, ?_⟩
  intro m w
  apply finiteSmoothFunctionEvaluation_injective F (B.size i)
  funext x
  change operatorRealizationFunctionEvaluation (R i) (slice m (ev w)) x = _
  exact (functionTensorSlice_evaluate E i
    (coefficientEvaluation_injective B R i) m (ev w) x).trans
    ((h w (Function.update m i x)).trans (translatedBlockLeviSlice_evaluation F B S i m (j w) x).symm)

section Actions

variable (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)

/-- The genuine single-block compact identity follows by comparing its one-block slices. -/
theorem isBlockPeriodCompactEvaluation_of_realizedLeviCoefficient
    (hj : ∀ a w, j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (h : IsRealizedLeviPeriodCoefficient B S R j ev) :
    IsBlockPeriodCompactEvaluation B (A.toMonoidHom.comp (compactOperator F n))
      (fun i => (R i).compactRepresentation) ev := by
  intro i k w
  refine eq_tensorCoordinateEnd_of_slices E (coefficientEvaluation_injective B R) i
    ((R i).compactRepresentation k) _ _ ?_
  intro m
  let slices := realizedLeviSlicesOfCoefficient B S R j ev h i
  change slices.slice m (A (compactOperator F n (blockShapeInfiniteCompactEmbedding B F i k)) w) =
    (R i).compactRepresentation k (slices.slice m w)
  exact slices.compact hj m k w

/-- The unnormalized infinitesimal equation holds in each full real block Lie algebra. -/
theorem blockPeriodRealLieEvaluation_of_realizedLeviCoefficient
    (hj : ∀ a w, j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (h : IsRealizedLeviPeriodCoefficient B S R j ev)
    (i : Fin B.length) (X : RealLieAlgebra F (B.size i)) (w : W) :
    ev (periodRealLieOperator A (blockShapeRealLieInclusion F B i X) w) =
      tensorCoordinateEnd i ((R i).lieAction X) (ev w) := by
  refine eq_tensorCoordinateEnd_of_slices E (coefficientEvaluation_injective B R) i
    ((R i).lieAction X) _ _ ?_
  intro m
  let slices := realizedLeviSlicesOfCoefficient B S R j ev h i
  change slices.slice m (A (differentialOperator F n (envelopingGenerator F n
    (complexify F n (blockShapeRealLieInclusion F B i X)))) w) =
    (R i).lieAction X (slices.slice m w)
  exact slices.realLie hj m X w

/-- Radical Lie directions vanish under the realized coefficient evaluation. -/
theorem blockPeriodStrictUpperEvaluation_of_realizedLeviCoefficient
    (hj : ∀ a w, j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (h : IsRealizedLeviPeriodCoefficient B S R j ev)
    (X : RealLieAlgebra F n) (hX : IsStrictUpperBlockLie F B X) (w : W) :
    ev (periodRealLieOperator A X w) = 0 := by
  apply functionTensorEvaluation_injective E (coefficientEvaluation_injective B R)
  rw [map_zero]
  funext m
  let a := differentialOperator F n (envelopingGenerator F n (complexify F n X))
  change functionTensorEvaluation E (ev (A a w)) m = 0
  rw [h (A a w), hj a w]
  exact congrFun (translatedBlockLeviRestriction_strictUpper F B S X hX (j w)) m

end Actions

section Restoration

variable (χ : Fin B.length → HeckeCharacter F)

private abbrev twistedBlock (i : Fin B.length) := (R i).heckeDeterminantTwist (χ i)

private abbrev blockTwistEquiv (i : Fin B.length) :=
  ((R i).heckeDeterminantTwistEquiv (χ i)).toLinearEquiv

private theorem functionTensorEvaluation_blockTwist
    (t : ⨂[ℂ] (i : Fin B.length), ↥((R i).Space)) (m : M) :
    functionTensorEvaluation (fun i => operatorRealizationFunctionEvaluation (twistedBlock B R χ i))
      (PiTensorProduct.congr (blockTwistEquiv B R χ) t) m =
      (∏ i, ((χ i).adelicDeterminant (B.size i) (m i) : ℂ)) * functionTensorEvaluation E t m := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, PiTensorProduct.congr_tprod,
      functionTensorEvaluation_tprod]
    have h (i : Fin B.length) :
        operatorRealizationFunctionEvaluation (twistedBlock B R χ i) (blockTwistEquiv B R χ i (x i))
          (m i) = ((χ i).adelicDeterminant (B.size i) (m i) : ℂ) * E i (x i) (m i) :=
      (R i).evaluate_heckeDeterminantTwistEquiv (χ i) (x i) (m i)
    simp_rw [h, Finset.prod_mul_distrib]
    ring
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]

/-- Undoing a block determinant twist restores evaluation of the actual
Levi period. The tensor equivalence is the product of the genuine
operator-realization twist equivalences. -/
theorem isRealizedLeviPeriodCoefficient_of_twistedEvaluation
    (h : ∀ (w : W) (m : M), functionTensorEvaluation E (ev w) m =
      (∏ i, ((χ i).adelicDeterminant (B.size i) (m i) : ℂ)) * P (j w) m) :
    IsRealizedLeviPeriodCoefficient B S (fun i => (R i).heckeDeterminantTwist (χ i)⁻¹) j
      ((PiTensorProduct.congr (blockTwistEquiv B R (fun i => (χ i)⁻¹))).toLinearMap.comp ev) := by
  intro w m
  change functionTensorEvaluation
    (fun i => operatorRealizationFunctionEvaluation ((R i).heckeDeterminantTwist (χ i)⁻¹))
    (PiTensorProduct.congr (blockTwistEquiv B R (fun i => (χ i)⁻¹)) (ev w)) m = _
  let c : ℂ := ∏ i, (((χ i)⁻¹).adelicDeterminant (B.size i) (m i) : ℂ)
  let d : ℂ := ∏ i, ((χ i).adelicDeterminant (B.size i) (m i) : ℂ)
  have hc : c * d = 1 := by
    change (∏ i, (((χ i)⁻¹).adelicDeterminant (B.size i) (m i) : ℂ)) *
      (∏ i, ((χ i).adelicDeterminant (B.size i) (m i) : ℂ)) = 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => Units.inv_mul ((χ i).adelicDeterminant (B.size i) (m i))
  refine (functionTensorEvaluation_blockTwist B R (fun i => (χ i)⁻¹) (ev w) m).trans ?_
  let z : ℂ := P (j w) m
  change c * functionTensorEvaluation E (ev w) m = z
  have hwt : functionTensorEvaluation E (ev w) m = d * z := h w m
  calc
    _ = c * (d * z) := congrArg (fun x : ℂ => c * x) hwt
    _ = (c * d) * z := (mul_assoc c d z).symm
    _ = 1 * z := congrArg (fun x : ℂ => x * z) hc
    _ = z := one_mul z

end Restoration

end Langlands.Global
