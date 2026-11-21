import Langlands.Automorphic.CuspidalLeviSliceFiniteness
import Langlands.Representation.TensorProduct.ProductFunctionLinearLift
import Langlands.Representation.TensorProduct.ProductFunctionSlices

/-! # The algebraic tensor of the actual cuspidal Levi coefficient -/

noncomputable section
universe u
open NumberField
open scoped Classical TensorProduct
set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL Langlands.GeneralLinear FiniteVectors
open OperatorRealization (heckeLieShift heckeLieShift_spec)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local instance cuspLeviTensorRationalGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviTensorContinuousGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviTensorSmoothGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviTensorStableGroup (d : ℕ) : AddCommGroup (StableAutomorphicFunctions F d) :=
  Submodule.addCommGroup _
local instance cuspLeviTensorFormsGroup (d : ℕ) : AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance cuspLeviTensorRealizationGroup {d : ℕ} (W : OperatorRealization F d) : AddCommGroup W.Space :=
  Submodule.addCommGroup _
local instance cuspLeviTensorOperatorRing (d : ℕ) : Ring (automorphicOperatorAlgebra F d) :=
  Subalgebra.toRing _

/-- Faithful evaluation of an actual realization as complex functions of adelic points. -/
def OperatorRealization.coefficientEvaluation {d : ℕ} (W : OperatorRealization F d) :
    W.Space →ₗ[ℂ] (AdelicGL F d → ℂ) :=
  (finiteSmoothFunctionEvaluation F d).comp (W.finiteSmoothAmbient F)

theorem OperatorRealization.coefficientEvaluation_injective {d : ℕ} (W : OperatorRealization F d) :
    Function.Injective (W.coefficientEvaluation F) :=
  (finiteSmoothFunctionEvaluation_injective F d).comp (W.finiteSmoothAmbient_injective F)

variable (B : BlockShape n) (S : OperatorRealization F n)
  {C : Type*} [AddCommGroup C] [Module ℂ C]
  (j : C →ₗ[ℂ] TranslatedBlockConstantTerms F B S)
  (μ : Fin B.length → HeckeCharacter F)

local notation "I" => Fin B.length
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Q" => translatedBlockLeviRestriction F B S
local notation "det" => fun (i : I) (x : AdelicGL F (B.size i)) => ((μ i).adelicDeterminant (B.size i) x : ℂ)

/-- The period on the Levi multiplied by all the block determinant characters. -/
def twistedLeviCoefficient : C →ₗ[ℂ] (M → ℂ) where
  toFun w m := (∏ i, (det) i (m i)) * Q (j w) m
  map_add' v w := by
    funext m
    have h := congrFun (((Q).comp j).map_add v w) m
    exact (congrArg ((∏ i, (det) i (m i)) * ·) h).trans (mul_add _ _ _)
  map_smul' c w := by
    funext m
    have h := congrFun (((Q).comp j).map_smul c w) m
    exact (congrArg ((∏ i, (det) i (m i)) * ·) h).trans (mul_left_comm _ _ _)

/-- The part of the twist depending on the fixed arguments outside the chosen block. -/
def complementaryDeterminantScalar (i : I) (m : M) : ℂ :=
  ∏ k ∈ Finset.univ.erase i, (det) k (m k)

private theorem determinant_product_update (i : I) (m : M) (x : AdelicGL F (B.size i)) :
    (∏ k, (det) k (Function.update m i x k)) =
      complementaryDeterminantScalar F B μ i m * (det) i x := by
  let f (k : I) := (det) k (Function.update m i x k)
  have h₁ : (∏ k ∈ Finset.univ.erase i, f k) = complementaryDeterminantScalar F B μ i m := by
    apply Finset.prod_congr rfl
    intro k hk
    exact congrArg ((det) k) (Function.update_of_ne (Finset.mem_erase.mp hk).1 _ _)
  exact (Finset.prod_erase_mul _ f (Finset.mem_univ i)).symm.trans
    (congrArg₂ (· * ·) h₁ (congrArg ((det) i) (Function.update_self i x m)))

variable {F B S j μ} {W : ∀ i : Fin B.length, OperatorRealization F (B.size i)}

local notation "W₁" => fun i : I => (W i).heckeDeterminantTwist (μ i)
local notation "f" => twistedLeviCoefficient F B S j μ
local notation "c" => complementaryDeterminantScalar F B μ

local instance cuspLeviTensorFactorGroups : ∀ i : I, AddCommGroup ((W₁) i).Space :=
  fun _ => Submodule.addCommGroup _

variable (D : ∀ i : Fin B.length, RealizedBlockLeviSlices F B S j i (W i))

local notation "e" => fun i : I => ((W₁) i).coefficientEvaluation F
local notation "he" => fun i : I => ((W₁) i).coefficientEvaluation_injective F
local notation "s" => fun i : I => (D i).twistedSlice (μ i)
local notation "Y" => PiTensorProduct ℂ (fun i : I => ((W₁) i).Space)

set_option maxHeartbeats 650000 in
private theorem twistedLeviCoefficient_slice (i : I) (m : M) (w : C) (x : AdelicGL F (B.size i)) :
    (e) i ((c) i m • (s) i m w) x = f w (Function.update m i x) := by
  calc
    _ = (c) i m * (e) i ((s) i m w) x := congrFun (((e) i).map_smul ((c) i m) _) x
    _ = (c) i m * ((det) i x * Q (j w) (Function.update m i x)) :=
      congrArg ((c) i m * ·) ((D i).twistedSlice_evaluation (μ i) m w x)
    _ = ((c) i m * (det) i x) * Q (j w) (Function.update m i x) := (mul_assoc _ _ _).symm
    _ = _ := congrArg (· * Q (j w) (Function.update m i x)) (determinant_product_update F B μ i m x).symm

set_option maxHeartbeats 770000 in
private theorem tensorSlice_eq_twistedSlice (g : C →ₗ[ℂ] Y)
    (hg : ∀ w m, functionTensorEvaluation e (g w) m = f w m) (i : I) (m : M) (w : C) :
    functionTensorSlice e i ((he) i) m (g w) = (c) i m • (s) i m w := by
  apply (he) i
  funext x
  exact (functionTensorSlice_evaluate e i ((he) i) m (g w) x).trans
    ((hg w (Function.update m i x)).trans (twistedLeviCoefficient_slice D i m w x).symm)

variable (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ C)

local notation "ρc" => (AlgHom.toMonoidHom' A).comp (compactOperator F n)
local notation "rOp" => fun (X : RealLieAlgebra F n) => differentialOperator F n
  (envelopingGenerator F n (complexify F n X))

set_option maxHeartbeats 850000 in
private theorem twistedSlice_realLie
    (hj : ∀ (a : automorphicOperatorAlgebra F n) w,
      j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (i : I) (X : RealLieAlgebra F (B.size i)) (m : M) (w : C) :
    (s) i m (A ((rOp) (blockShapeRealLieInclusion F B i X)) w) =
      ((W₁) i).lieAction X ((s) i m w) + (-heckeLieShift (μ i) X) • (s) i m w := by
  let R := W i
  let x := (D i).slice m w
  let E := R.heckeDeterminantTwistEquiv (μ i)
  let b := heckeLieShift (μ i) X
  let y := (D i).slice m (A ((rOp) (blockShapeRealLieInclusion F B i X)) w)
  have hxy : y = R.lieAction X x := (D i).realLie hj m X w
  have h := R.lieAction_heckeDeterminantTwistEquiv (μ i) X (heckeLieShift_spec (μ i) X) x
  have h' : ((W₁) i).lieAction X (E x) = E y + b • E x := by
    calc
      _ = E (R.lieAction X x + b • x) := h
      _ = E (y + b • x) := congrArg (fun z => E (z + b • x)) hxy.symm
      _ = _ := (E.map_add _ _).trans (congrArg (E y + ·) (E.map_smul b x))
  change E y = ((W₁) i).lieAction X (E x) + (-b) • E x
  let l := ((W₁) i).lieAction X (E x)
  exact ((eq_sub_iff_add_eq).mpr h'.symm).trans
    ((sub_eq_add_neg l (b • E x)).trans (congrArg (l + ·) (neg_smul b (E x)).symm))

private theorem smul_add_sub_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a b : ℂ) (x y : V) : a • (x + b • y) - b • (a • y) = a • x := by
  rw [smul_add, smul_comm a b, add_sub_cancel_right]

include D in
set_option maxHeartbeats 900000 in
/-- The tensor real Lie derivative is the genuine single-block derivative with its scalar shift. -/
theorem twistedLeviTensor_realLie
    (hj : ∀ (a : automorphicOperatorAlgebra F n) w,
      j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (g : C →ₗ[ℂ] Y) (hg : ∀ w m, functionTensorEvaluation e (g w) m = f w m)
    (i : I) (X : RealLieAlgebra F (B.size i)) (w : C) :
    g (A ((rOp) (blockShapeRealLieInclusion F B i X)) w) =
      tensorCoordinateEnd i (((W₁) i).complexLieAction (complexify F (B.size i) X)) (g w) +
        (-heckeLieShift (μ i) X) • g w := by
  let y := A ((rOp) (blockShapeRealLieInclusion F B i X)) w
  let b := -heckeLieShift (μ i) X
  let a := ((W₁) i).lieAction X
  have h : g y - b • g w = tensorCoordinateEnd i a (g w) := by
    apply eq_tensorCoordinateEnd_of_slices e he i a (g y - b • g w) (g w)
    intro m
    let t := functionTensorSlice e i ((he) i) m
    let z := (s) i m w
    have hy : t (g y) = (c) i m • (a z + b • z) :=
      (tensorSlice_eq_twistedSlice D g hg i m y).trans
        (congrArg ((c) i m • ·) (twistedSlice_realLie D A hj i X m w))
    have hw : t (g w) = (c) i m • z := tensorSlice_eq_twistedSlice D g hg i m w
    calc
      t (g y - b • g w) = t (g y) - b • t (g w) :=
        (t.map_sub _ _).trans (congrArg (t (g y) - ·) (t.map_smul _ _))
      _ = (c) i m • (a z + b • z) - b • ((c) i m • z) :=
        congrArg₂ (fun (x y : ((W₁) i).Space) => x - b • y) hy hw
      _ = (c) i m • a z := smul_add_sub_smul ((c) i m) b (a z) z
      _ = a (t (g w)) := (a.map_smul _ _).symm.trans (congrArg a hw.symm)
  exact eq_add_of_sub_eq h

variable [CompactSpace (AdeleQuotient F)]

include D in
set_option maxHeartbeats 950000 in
/-- The twisted product-Levi coefficient has a unique algebraic evaluation tensor. -/
theorem exists_twistedLeviCoefficientTensor
    (hj : ∀ (a : automorphicOperatorAlgebra F n) w,
      j (A a w) = translatedBlockTermOperatorAction F B S a (j w))
    (hκ : ∀ w : C, IsFiniteVector ρc w)
    (hW : ∀ i : I, ((W₁) i).IsCuspidal) (χ : I → HeckeCharacter F)
    (hχ : ∀ i, (χ i).IsUnitary) (hχW : ∀ i, ((W₁) i).HasCentralCharacter (χ i)) :
    ∃ g : C →ₗ[ℂ] Y, ∀ w m, functionTensorEvaluation e (g w) m = f w m := by
  have h : ∀ w : C, ∃ P : ∀ i : I, Submodule ℂ ((W₁) i).Space,
      (∀ i, FiniteDimensional ℂ (P i)) ∧ ∀ i m,
      ∃ v : P i, (e) i v.val = fun x => f w (Function.update m i x) := by
    intro w
    choose P hP hmem using fun i : I =>
      exists_finiteDimensional_twistedSliceSpace F B S j i (D i) (μ i) A hj
        (hW i) (χ i) (hχ i) (hχW i) w (hκ w)
    refine ⟨P, hP, fun i m => ⟨⟨(c) i m • (s) i m w, (P i).smul_mem _ (hmem i m)⟩, ?_⟩⟩
    funext x
    exact twistedLeviCoefficient_slice D i m w x
  obtain ⟨g, hg⟩ := exists_linearTensor_of_finiteDimensional_slices e he f h
  exact ⟨g, fun w m => congrFun (hg w) m⟩

end Langlands.Automorphic
