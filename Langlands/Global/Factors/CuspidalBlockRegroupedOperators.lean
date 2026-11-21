import Langlands.Global.Factors.CuspidalBlockPlaceCoefficients
import Langlands.Global.Factors.GroupedTensorOperatorRegrouping

/-! # One-place Lie operators on regrouped cuspidal block tensors -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 210000
set_option synthInstance.maxHeartbeats 58000
set_option Elab.async false

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL AdelicBlockParabolic InfinitePlaceFamily
open AdelicBlockScalarSections
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "S" => (fun i : Fin k => CuspidalOperatorRealization.realization (T i))
local notation "CF" => (fun i : Fin k => BlockInducedReferences.BlockCoefficients D i)
local notation "CI" => (fun (p : Index F) (i : Fin k) => InfiniteBlockCoefficient T i p)

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup _
private local instance {n : ℕ} {v : FinitePlace F} (R : LocalRealization F n v) : AddCommGroup R.Space :=
  Submodule.addCommGroup _
private local instance (p : Index F) (i : Fin k) : AddCommGroup (CI p i) := Submodule.addCommGroup _
private local instance finiteBlockGroup (i : Fin k) : AddCommGroup (CF i) :=
  DirectLimit.instAddCommGroupOfAddMonoidHomClass

local notation "FinCoeff" => (⨂[ℂ] i, CF i)
local notation "InfCoeff" => (⨂[ℂ] p, InfinitePlaceCoefficients T p)
local notation "V" => (fun i : Fin k => OperatorRealization.Space (S i))
local notation "U" => (⨂[ℂ] i, V i)

/-- The actual place coefficient tensor with the factors regrouped by cuspidal block. -/
def groupedBlockTensorEquiv : FinCoeff ⊗[ℂ] InfCoeff ≃ₗ[ℂ] U :=
  (groupedCoefficientEquiv hm P h).trans (coefficientEquiv F B S).symm

local notation "L" => groupedBlockTensorEquiv hm P h

theorem coefficientEquiv_groupedBlockTensorEquiv (x : FinCoeff ⊗[ℂ] InfCoeff) :
    coefficientEquiv F B S (L x) = groupedCoefficientEquiv hm P h x :=
  (coefficientEquiv F B S).apply_symm_apply _

theorem groupedBlockTensorEquiv_pure (a : ∀ i, CF i) (c : ∀ p i, CI p i) :
    L (groupedPure a c) = PiTensorProduct.tprod ℂ (fun i => blockVectorEquiv hm P h i
      (a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => c p i))) := by
  apply (coefficientEquiv F B S).injective
  apply Subtype.ext
  funext z
  have h₁ := congrArg (fun x : coefficientValues F B S => x.val z)
    (coefficientEquiv_groupedBlockTensorEquiv hm P h (groupedPure a c))
  have h₂ := groupedCoefficientEquiv_tprod hm P h a c z
  have h₃ := coefficientEquiv_tprod_apply F B S
    (fun i => blockVectorEquiv hm P h i (a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun p => c p i)) z
  exact h₁.trans (h₂.trans h₃.symm)

private theorem blockVectorEquiv_placeLie_update (i : Fin k) (p : Index F)
    (Y : Lie (m i + 1) p) (a : CF i) (c : ∀ q, CI q i) :
    blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ
      (Function.update c p ((T i).placeDensityModels.sourceLie p Y (c p)))) =
      (S i).placeLieFamily p Y (blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c)) := by
  let d := Function.update c p ((T i).placeDensityModels.sourceLie p Y (c p))
  let e := (blockTensorPresentationEquiv hm P i).toLinearEquiv
  let Q := (P i).allPlaceTensorEquiv (h i)
  have he (b : ⨂[ℂ] q, CI q i) : blockVectorEquiv hm P h i (a ⊗ₜ[ℂ] b) = Q (e a ⊗ₜ[ℂ] b) :=
    congrArg Q (TensorProduct.congr_tmul e (LinearEquiv.refl ℂ _) a b)
  have hlocal : d p = (T i).placeDensityModels.sourceLie p Y (c p) := Function.update_self ..
  have hother (q : Index F) (hq : q ≠ p) : d q = c q := Function.update_of_ne hq ..
  exact (he _).trans (((P i).allPlaceTensorEquiv_lie (h i) p Y (e a) c d hother hlocal).trans
    (congrArg ((S i).placeLieFamily p Y) (he _).symm))

/-- The actual one-place Lie sum retains the block operators under regrouping. -/
theorem groupedBlockTensorEquiv_placeLie (p : Index F) (Y : ∀ i, Lie (m i + 1) p)
    (a : FinCoeff) (b : InfCoeff) :
    L (a ⊗ₜ[ℂ] groupedPlaceOperator p (fun i => (T i).placeDensityModels.sourceLie p (Y i)) b) =
      (∑ i, FiniteTensor.slotAlgebraHom i ((S i).placeLieFamily p (Y i))) (L (a ⊗ₜ[ℂ] b)) := by
  let e := fun i : Fin k => (blockVectorEquiv hm P h i).toLinearMap
  let X := fun i : Fin k => (T i).placeDensityModels.sourceLie p (Y i)
  let Z := fun i : Fin k => (S i).placeLieFamily p (Y i)
  have he := @groupedPlaceOperator_intertwines (Fin k) (Index F) CF (fun p i => ↥(CI p i))
    (fun i => finiteBlockGroup hm P i) (fun _ => inferInstance)
    (fun p i => Submodule.addCommGroup (CI p i)) (fun p i => Submodule.module (CI p i))
    V (fun i => Submodule.addCommGroup (S i).Space) (fun i => Submodule.module (S i).Space)
    inferInstance inferInstance (Fin.fintype k) inferInstance (L).toLinearMap e
    (groupedBlockTensorEquiv_pure hm P h) p X Z
    (fun i => blockVectorEquiv_placeLie_update hm P h i p (Y i))
  have hv := LinearMap.congr_fun he (a ⊗ₜ[ℂ] b)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul] using hv

end Langlands.Global.CuspidalBlockInduction
