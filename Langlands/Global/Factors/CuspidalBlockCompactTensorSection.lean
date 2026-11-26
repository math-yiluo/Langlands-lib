import Langlands.Global.Factors.CuspidalBlockCompactTensorComparison
import Langlands.Global.Factors.CuspidalBlockGroupedFiniteEvaluation
import Langlands.Global.AdelicBlockCompactTensorMap

/-! # Cuspidal compact evaluations as normalized adelic sections -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 240000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 70000

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic NumberField InfinitePlaceFamily LocalFactor.Archimedean ArchimedeanGL
open FiniteAdelicGL GeneralLinear PrimitiveAdelicHeight AdelicBlockParabolic
open AdelicBlockScalarSections AdelicBlockDeterminantCharacter
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

private theorem compactTensorValue_covariance_of_coordinates
    (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
    (W : Submodule ℂ (FullLevi F B → ℂ))
    {Af Ai Vf Vi : Type u}
    [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]
    (ef : ↥(FiniteAdelicGL.standardIntegral F n) → Af →ₗ[ℂ] Vf)
    (ei : ↥(standardInfiniteCompact F n) → Ai →ₗ[ℂ] Vi)
    (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] W)
    (hc : ∀ (p : compactIntersection B F) (k : standardCompact F n)
        (z : FullLevi F B) (a : Af) (b : Ai),
      let x := standardCompactProductEquiv F n (⟨p.val.val, p.property⟩ * k)
      let y := standardCompactProductEquiv F n k
      (e (ef x.2 a ⊗ₜ[ℂ] ei x.1 b)).val z =
        (e (ef y.2 a ⊗ₜ[ℂ] ei y.1 b)).val (z * B.leviProjection (Adeles F) p.val))
    (p : compactIntersection B F) (k : standardCompact F n)
    (z : FullLevi F B) (a : Af) (b : Ai) :
    (compactTensorValue F B W ef ei e (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val z =
      (compactTensorValue F B W ef ei e k (a ⊗ₜ[ℂ] b)).val
        (z * B.leviProjection (Adeles F) p.val) := by
  rw [compactTensorValue_tmul, compactTensorValue_tmul]
  exact hc p k z a b

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)
variable (hr : ∀ v i, (T i).realization.HasRealPlaceParameter v (real v i))
variable (hc : ∀ v i, (T i).realization.HasComplexPlaceParameter v (complex v i))

local notation "n" => r + 1
local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P
local notation "S" => (fun i : Fin k => CuspidalOperatorRealization.realization (T i))
local notation "K" => standardCompact F n
local notation "Ki" => standardInfiniteCompact F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n
local notation "M" => FullLevi F B
local notation "Gf" => FiniteAdelicGL F n
local notation "W" => coefficientValues F B S
local notation "CI" => (fun (p : Index F) (i : Fin k) => InfiniteBlockCoefficient T i p)

private local instance (j : ℕ) : AddCommGroup (RationalInvariantFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (ContinuousRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (AutomorphicForms F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (StableAutomorphicFunctions F j) := Submodule.addCommGroup _
private local instance {j : ℕ} (V : OperatorRealization F j) : AddCommGroup V.Space := Submodule.addCommGroup _
private local instance (p : Index F) (i : Fin k) : AddCommGroup (CI p i) := Submodule.addCommGroup _

local notation "InfiniteStandardTensor" => (⨂[ℂ] p, infiniteStandardSpace r real complex p)
local notation "Fi" => (⨂[ℂ] p, InfinitePlaceCoefficients T p)
local notation "Ff" => (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients D i)
private local instance (p : Index F) : AddCommGroup (InfinitePlaceCoefficients T p) :=
  PiTensorProduct.instAddCommGroup

local notation "ei" => infiniteEvaluation real complex hm T hr hc

variable {Af : Type u} [AddCommGroup Af] [Module ℂ Af]
variable (ef : FiniteAdelicGL F (r + 1) → Af →ₗ[ℂ]
  (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients (finiteReferences hm P) i))

private local instance : AddCommGroup Ff := groupedFiniteCoefficientGroup D
private local instance : AddCommGroup Fi := PiTensorProduct.instAddCommGroup
private local instance : AddCommGroup InfiniteStandardTensor := PiTensorProduct.instAddCommGroup

local notation "e" => (groupedCoefficientEquiv hm P h).toLinearMap
local notation "efK" => (fun q : Kf => ef q.val)

variable (hl : HasFiniteScalarCovariance hm P h ef)

include hl in
/-- The evaluated compact tensor satisfies the left covariance of the scalar
section model. -/
theorem cuspidalCompactTensorValue_covariance (p : compactIntersection B F) (q : K) (z : M)
    (a : Af) (b : InfiniteStandardTensor) :
    (compactTensorValue F B W efK ei e (⟨p.val.val, p.property⟩ * q) (a ⊗ₜ[ℂ] b)).val z =
      (compactTensorValue F B W efK ei e q (a ⊗ₜ[ℂ] b)).val
        (z * GeneralLinear.BlockShape.leviProjection B (Adeles F) p.val) := by
  let coordinateLaw := @compactEvaluation_left F _ _ _ r k m hm T P h
    real complex hr hc Af _ _ ef hl
  exact compactTensorValue_covariance_of_coordinates F B W efK ei e coordinateLaw p q z a b

/-- Extend the compact evaluation to the full scalar adelic section model. -/
def cuspidalCompactTensorSectionMap (hleft : HasFiniteScalarCovariance hm P h ef) :
    Af ⊗[ℂ] InfiniteStandardTensor →ₗ[ℂ] ScalarSections F B W := by
  let cov := @cuspidalCompactTensorValue_covariance F _ _ _ r k m hm T P h
    real complex hr hc Af _ _ ef hleft
  exact @compactTensorSectionMap F _ _ n B W Af InfiniteStandardTensor Ff Fi
    _ _ _ _ _ _ _ _ efK ei e cov

end Langlands.Global.CuspidalBlockInduction
