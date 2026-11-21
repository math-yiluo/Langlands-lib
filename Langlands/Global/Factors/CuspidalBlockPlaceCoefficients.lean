import Langlands.Automorphic.CuspidalPresentationTensorDecomposition
import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Global.Factors.CuspidalBlockInductionReferences
import Langlands.Representation.Induction.BinaryProductTensor

/-! # Placewise tensors of the realized cuspidal Levi coefficients -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

universe u uQ v w

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL AdelicBlockParabolic
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

section Regrouping

open Induction.BinaryTensor

variable {I : Type v} [Finite I] (A C : I → Type w)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
variable [∀ i, AddCommGroup (C i)] [∀ i, Module ℂ (C i)]

private def combineBlockTensors :
    (⨂[ℂ] i, A i) ⊗[ℂ] (⨂[ℂ] i, C i) ≃ₗ[ℂ] (⨂[ℂ] i, A i ⊗[ℂ] C i) :=
  (tensorEquivDep ℂ (fun j => ⨂[ℂ] i, family (A i) (C i) j)).trans
    ((FiniteTensor.transposeLinearEquiv ℂ
      (fun j i => family (A i) (C i) j)).trans
      (PiTensorProduct.congr fun i => (tensorEquiv ℂ (A i) (C i)).symm))

private theorem combineBlockTensors_tprod (a : ∀ i, A i) (c : ∀ i, C i) :
    combineBlockTensors A C (PiTensorProduct.tprod ℂ a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      PiTensorProduct.tprod ℂ (fun i => a i ⊗ₜ[ℂ] c i) := by
  let x (i : I) := tuple (a i) (c i)
  change combineBlockTensors A C
    (PiTensorProduct.tprod ℂ (fun i => x i (.inl ())) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun i => x i (.inr ()))) = _
  have h := tensorEquivDep_tprod ℂ (fun j => ⨂[ℂ] i, family (A i) (C i) j)
    (fun j => PiTensorProduct.tprod ℂ (fun i => x i j))
  simp only [combineBlockTensors, LinearEquiv.trans_apply, h,
    FiniteTensor.transposeLinearEquiv_tprod, PiTensorProduct.congr_tprod]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext i
  exact (LinearEquiv.symm_apply_eq _).mpr (tensorEquiv_tmul ℂ (A i) (C i) (a i) (c i)).symm

variable {J : Type w} [Finite J]
variable (M : J → I → Type w) [∀ p i, AddCommGroup (M p i)] [∀ p i, Module ℂ (M p i)]

private def groupPlaceTensors :
    (⨂[ℂ] i, A i) ⊗[ℂ] (⨂[ℂ] p, (⨂[ℂ] i, M p i)) ≃ₗ[ℂ]
      (⨂[ℂ] i, A i ⊗[ℂ] (⨂[ℂ] p, M p i)) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ _)
    (FiniteTensor.transposeLinearEquiv ℂ M)).trans
      (combineBlockTensors A (fun i => ⨂[ℂ] p, M p i))

private theorem groupPlaceTensors_tprod (a : ∀ i, A i) (c : ∀ p i, M p i) :
    groupPlaceTensors A M (PiTensorProduct.tprod ℂ a ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun p => PiTensorProduct.tprod ℂ (c p))) =
      PiTensorProduct.tprod ℂ (fun i => a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => c p i)) := by
  simp only [groupPlaceTensors, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, FiniteTensor.transposeLinearEquiv_tprod, combineBlockTensors_tprod]

end Regrouping

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ}
variable (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "S" => (fun (i : Fin k) => CuspidalOperatorRealization.realization (T i))

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (A : OperatorRealization F n) : AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- The genuine infinite coefficient for a block at one specified place. -/
abbrev InfiniteBlockCoefficient (T : ∀ i, CuspidalOperatorRealization F (m i))
    (i : Fin k) (p : InfinitePlaceFamily.Index F) :=
  (T i).placeDensityModels.subspace p

local instance (i : Fin k) (p : InfinitePlaceFamily.Index F) :
    AddCommGroup (InfiniteBlockCoefficient T i p) := Submodule.addCommGroup _

/-- The coefficient tensor at one infinite place, in the original block order. -/
abbrev InfinitePlaceCoefficients (T : ∀ i, CuspidalOperatorRealization F (m i))
    (p : InfinitePlaceFamily.Index F) :=
  ⨂[ℂ] i, InfiniteBlockCoefficient T i p

local notation "CF" => (fun i : Fin k => BlockInducedReferences.BlockCoefficients D i)
local notation "CI" => (fun i : Fin k => ⨂[ℂ] p, InfiniteBlockCoefficient T i p)

/-- The exact finite presentation and the chosen infinite factors realize one block. -/
def blockVectorEquiv (i : Fin k) :
    CF i ⊗[ℂ] CI i ≃ₗ[ℂ] (T i).Space :=
  (TensorProduct.congr (blockTensorPresentationEquiv hm P i).toLinearEquiv
    (LinearEquiv.refl ℂ _)).trans ((P i).allPlaceTensorEquiv (h i))

/-- The realized scalar Levi coefficients, grouped into the finite adelic factor
and the tensor of coefficient spaces at the infinite places. -/
def groupedCoefficientEquiv :
    (⨂[ℂ] i, CF i) ⊗[ℂ] (⨂[ℂ] p, InfinitePlaceCoefficients T p) ≃ₗ[ℂ]
      AdelicBlockScalarSections.coefficientValues F B S :=
  (groupPlaceTensors CF (fun p i => InfiniteBlockCoefficient T i p)).trans
    ((PiTensorProduct.congr (blockVectorEquiv hm P h)).trans
      (AdelicBlockScalarSections.coefficientEquiv F B S))

/-- Pure place factors evaluate as the product of the corresponding realized
block vectors, with each block's infinite factors kept in their own places. -/
theorem groupedCoefficientEquiv_tprod (a : ∀ i, CF i)
    (c : ∀ p i, InfiniteBlockCoefficient T i p) (z : FullLevi F B) :
    (groupedCoefficientEquiv hm P h
      (PiTensorProduct.tprod ℂ a ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun p => PiTensorProduct.tprod ℂ (c p)))).val z =
      AdelicBlockScalarSections.blockCoefficient F B S
        (fun i => blockVectorEquiv hm P h i
          (a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => c p i))) z := by
  let e := AdelicBlockScalarSections.coefficientEquiv F B S
  let t := PiTensorProduct.congr (blockVectorEquiv hm P h)
  let x (i : Fin k) := a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => c p i)
  have h₁ := congrArg (fun y => (e (t y)).val z)
    (groupPlaceTensors_tprod CF (fun p i => InfiniteBlockCoefficient T i p) a c)
  have h₂ := congrArg (fun y => (e y).val z) (PiTensorProduct.congr_tprod
    (blockVectorEquiv hm P h) x)
  exact h₁.trans (h₂.trans (AdelicBlockScalarSections.coefficientEquiv_tprod_apply F B S _ z))

/-- Translating the finite tensor of a block gives its actual finite right translate. -/
theorem blockVectorEquiv_finite (i : Fin k) (d : FiniteAdelicGL F (m i + 1))
    (a : CF i) (c : CI i) :
    blockVectorEquiv hm P h i (BlockInducedReferences.blockRepresentation D i d a ⊗ₜ[ℂ] c) =
      (T i).realization.finiteRepresentation d (blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] c)) := by
  let e := blockTensorPresentationEquiv hm P i
  let q := (P i).allPlaceTensorEquiv (h i)
  have hcomp (v : CF i) : blockVectorEquiv hm P h i (v ⊗ₜ[ℂ] c) = q (e v ⊗ₜ[ℂ] c) :=
    congrArg q (TensorProduct.congr_tmul e.toLinearEquiv (LinearEquiv.refl ℂ _) v c)
  have he := Representation.IntertwiningMap.isIntertwining _ _
    e.toIntertwiningMap d a
  exact (hcomp _).trans ((congrArg (fun v => q (v ⊗ₜ[ℂ] c)) he).trans
    (((P i).allPlaceTensorEquiv_finite (h i) d (e a) c).trans
      (congrArg ((T i).realization.finiteRepresentation d) (hcomp a).symm)))

end Langlands.Global.CuspidalBlockInduction
