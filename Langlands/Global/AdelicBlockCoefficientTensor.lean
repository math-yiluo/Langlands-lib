import Langlands.Global.AdelicBlockScalarSections
import Langlands.Representation.Classification.LeftCuspidalDerivative.Criterion
import Langlands.Representation.Tensor.FiniteEquivalences

/-!
# The coefficient tensor of scalar adelic block sections

Evaluation identifies the algebraic tensor of actual block realizations with
the subspace of scalar Levi functions spanned by their product coefficients.
-/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uV uX

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Classification.LeftCuspidalDerivative (tensorEval tensorEval_tmul tensorEval_injective)

section Evaluation

variable {r : ℕ} {V : Fin r → Type uV} {X : Fin r → Type uX}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Evaluate a tensor by multiplying the evaluations on its coordinates. -/
def indexedEvaluation (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ)) :
    (⨂[ℂ] i, V i) →ₗ[ℂ] ((∀ i, X i) → ℂ) :=
  LinearMap.pi fun x =>
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin r) ℂ).compLinearMap
      (fun i => (LinearMap.proj (x i)).comp (e i)))

@[simp]
theorem indexedEvaluation_tprod (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ))
    (v : ∀ i, V i) (x : ∀ i, X i) :
    indexedEvaluation e (PiTensorProduct.tprod ℂ v) x = ∏ i, e i (v i) (x i) := by
  simp only [indexedEvaluation, LinearMap.pi_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    MultilinearMap.mkPiAlgebra_apply]

/-- Coordinatewise pullback on the evaluation functions is given by the tensor
of the corresponding linear maps on the coefficients. -/
theorem indexedEvaluation_map_apply (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ))
    (L : ∀ i, V i →ₗ[ℂ] V i) (g : ∀ i, X i → X i)
    (h : ∀ i v x, e i (L i v) x = e i v (g i x)) (t : ⨂[ℂ] i, V i) (x : ∀ i, X i) :
    indexedEvaluation e (PiTensorProduct.map L t) x = indexedEvaluation e t (fun i => g i (x i)) := by
  have hmap :
      LinearMap.proj x ∘ₗ indexedEvaluation e ∘ₗ PiTensorProduct.map L =
        LinearMap.proj (fun i => g i (x i)) ∘ₗ indexedEvaluation e := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      PiTensorProduct.map_tprod, indexedEvaluation_tprod, h]
  exact LinearMap.congr_fun hmap t

private theorem indexedEvaluation_cons {r : ℕ} {V : Fin (r + 1) → Type uV}
    {X : Fin (r + 1) → Type uX} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ)) (t : ⨂[ℂ] i, V i)
    (x : X 0) (xs : ∀ i : Fin r, X i.succ) :
    indexedEvaluation e t (Fin.cons x xs) =
      e 0 (tensorEval (indexedEvaluation (fun i : Fin r => e i.succ))
        (FiniteTensor.headTailLinearEquiv ℂ V t) xs) x := by
  have h :
      LinearMap.proj (Fin.cons x xs) ∘ₗ indexedEvaluation e =
        LinearMap.proj x ∘ₗ e 0 ∘ₗ LinearMap.proj xs ∘ₗ
          tensorEval (indexedEvaluation (fun i : Fin r => e i.succ)) ∘ₗ
          (FiniteTensor.headTailLinearEquiv ℂ V).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      indexedEvaluation_tprod, FiniteTensor.headTailLinearEquiv_tprod, LinearEquiv.coe_coe,
      tensorEval_tmul, map_smul, smul_eq_mul, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ, mul_comm]
  exact LinearMap.congr_fun h t

/-- Injective evaluations on each factor jointly distinguish tensors. -/
theorem indexedEvaluation_injective (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ))
    (he : ∀ i, Function.Injective (e i)) : Function.Injective (indexedEvaluation e) := by
  induction r with
  | zero =>
    let x : ∀ i : Fin 0, X i := fun i => i.elim0
    let E : (⨂[ℂ] i, V i) ≃ₗ[ℂ] ℂ := PiTensorProduct.isEmptyEquiv (Fin 0)
    have h : LinearMap.proj x ∘ₗ indexedEvaluation e = E.toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro v
      simp [E]
    intro s t hst
    apply E.injective
    rw [← LinearEquiv.coe_coe, ← h, LinearMap.comp_apply, LinearMap.comp_apply, hst]
  | succ r ih =>
    let E := FiniteTensor.headTailLinearEquiv ℂ V
    let tail := indexedEvaluation (fun i : Fin r => e i.succ)
    have htail : Function.Injective tail := ih _ (fun i => he i.succ)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    apply E.injective
    apply tensorEval_injective tail htail
    rw [map_zero, map_zero]
    funext xs
    apply he 0
    funext x
    rw [← indexedEvaluation_cons, ht]
    simp

end Evaluation

section ActualCoefficients

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local instance (t : ℕ) : AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F t) :=
  Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance {t : ℕ} (T : OperatorRealization F t) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

private def factorEvaluation (i : Fin B.length) :
    (S i).Space →ₗ[ℂ] (AdelicGL F (B.size i) → ℂ) where
  toFun f g := ContinuousRationalFunctions.evaluate F (B.size i) ((S i).toContinuous f) g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem factorEvaluation_injective (i : Fin B.length) :
    Function.Injective (factorEvaluation F B S i) := by
  intro f g h
  apply (S i).toContinuous_injective
  apply ContinuousRationalFunctions.toContinuousMap_injective
  apply ContinuousMap.ext
  exact congrFun h

/-- Evaluate the tensor of the actual block realizations as a scalar Levi function. -/
def coefficientEvaluation :
    (⨂[ℂ] i, (S i).Space) →ₗ[ℂ] (AdelicBlockParabolic.FullLevi F B → ℂ) :=
  indexedEvaluation (factorEvaluation F B S)

@[simp]
theorem coefficientEvaluation_tprod (v : ∀ i, (S i).Space) :
    coefficientEvaluation F B S (PiTensorProduct.tprod ℂ v) = blockCoefficient F B S v := by
  funext m
  exact indexedEvaluation_tprod _ v m

theorem coefficientEvaluation_injective :
    Function.Injective (coefficientEvaluation F B S) :=
  indexedEvaluation_injective _ (factorEvaluation_injective F B S)

/-- The coefficient evaluation intertwines blockwise finite right translation. -/
theorem coefficientEvaluation_finite (d : FiniteLevi F B) (t : ⨂[ℂ] i, (S i).Space)
    (m : FullLevi F B) :
    coefficientEvaluation F B S (PiTensorProduct.map (fun i =>
      (S i).finiteRepresentation (d i)) t) m =
    coefficientEvaluation F B S t (m * leviPair F B 1 d) :=
  indexedEvaluation_map_apply (factorEvaluation F B S) _
    (fun i x => x * AdelicGL.ofFinite F (B.size i) (d i))
    (fun i v x => OperatorRealization.evaluate_finiteRepresentation (S i) (d i) v x) t m

/-- The coefficient evaluation intertwines blockwise infinite compact right translation. -/
theorem coefficientEvaluation_compact
    (k : ∀ i : Fin B.length, standardInfiniteCompact F (B.size i))
    (t : ⨂[ℂ] i, (S i).Space) (m : FullLevi F B) :
    coefficientEvaluation F B S (PiTensorProduct.map (fun i =>
      (S i).compactRepresentation (k i)) t) m =
    coefficientEvaluation F B S t (m * leviPair F B (fun i => (k i).val) 1) :=
  indexedEvaluation_map_apply (factorEvaluation F B S) _
    (fun i x => x * AdelicGL.ofInfinite F (B.size i) (k i).val)
    (fun i v x => OperatorRealization.evaluate_compactRepresentation (S i) (k i) v x) t m

theorem range_coefficientEvaluation :
    LinearMap.range (coefficientEvaluation F B S) = coefficientValues F B S := by
  rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span, ← Set.range_comp, coefficientValues]
  congr 2
  funext v
  exact coefficientEvaluation_tprod F B S v

/-- The tensor of the inducing realizations is equivalent to its scalar coefficient space. -/
def coefficientEquiv : (⨂[ℂ] i, (S i).Space) ≃ₗ[ℂ] coefficientValues F B S :=
  (LinearEquiv.ofInjective (coefficientEvaluation F B S)
    (coefficientEvaluation_injective F B S)).trans
      (LinearEquiv.ofEq _ _ (range_coefficientEvaluation F B S))

@[simp]
theorem coefficientEquiv_tprod_apply (v : ∀ i, (S i).Space)
    (m : AdelicBlockParabolic.FullLevi F B) :
    (coefficientEquiv F B S (PiTensorProduct.tprod ℂ v)).val m = blockCoefficient F B S v m :=
  congrFun (coefficientEvaluation_tprod F B S v) m

end ActualCoefficients

end Langlands.Global.AdelicBlockScalarSections
