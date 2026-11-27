import Langlands.Global.AdelicBlockCompactTensorSmoothEmbedding
import Langlands.Global.Factors.CuspidalBlockCompactTensorSection
import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluationFaithfulness
import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluationSmooth

/-! # Smooth sections from the cuspidal block tensor -/

noncomputable section

open scoped BigOperators Classical ContDiff Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 70000
set_option linter.all false

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic NumberField InfinitePlaceFamily LocalFactor.Archimedean ArchimedeanGL
open FiniteAdelicGL GeneralLinear AdelicBlockParabolic AdelicBlockScalarSections
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

attribute [local instance] LocalRealization.localRealizationSpaceAddCommGroup

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
local notation "Ki" => standardInfiniteCompact F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n
local notation "Gf" => FiniteAdelicGL F n
local notation "CI" => (fun (p : Index F) (i : Fin k) => InfiniteBlockCoefficient T i p)

private local instance (j : ℕ) : AddCommGroup (RationalInvariantFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (ContinuousRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (AutomorphicForms F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (StableAutomorphicFunctions F j) := Submodule.addCommGroup _
private local instance {j : ℕ} (V : OperatorRealization F j) : AddCommGroup V.Space := Submodule.addCommGroup _
private local instance (p : Index F) (i : Fin k) : AddCommGroup (CI p i) := Submodule.addCommGroup _
private local instance (p : Index F) : AddCommGroup (InfinitePlaceCoefficients T p) :=
  PiTensorProduct.instAddCommGroup

local notation "Ai" => (⨂[ℂ] p, infiniteStandardSpace r real complex p)
local notation "Vi" => (⨂[ℂ] p, InfinitePlaceCoefficients T p)
local notation "Vf" => (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients D i)
private local instance (i : Fin k) : AddCommGroup (BlockInducedReferences.BlockCoefficients D i) :=
  DirectLimit.instAddCommGroupOfAddMonoidHomClass
private local instance (i : Fin k) : Module ℂ (BlockInducedReferences.BlockCoefficients D i) :=
  inferInstance
private local instance : AddCommGroup Vf := groupedFiniteCoefficientGroup D
private local instance : Module ℂ Vf := PiTensorProduct.instModule
private local instance : AddCommGroup Vi := PiTensorProduct.instAddCommGroup
private local instance : Module ℂ Vi := PiTensorProduct.instModule
private local instance : AddCommGroup Ai := PiTensorProduct.instAddCommGroup
private local instance : Module ℂ Ai := PiTensorProduct.instModule

local notation "ei" => infiniteEvaluation real complex hm T hr hc
local notation "e" => (groupedCoefficientEquiv hm P h).toLinearMap
local notation "κ" => infiniteStandardAction r real complex

variable {Af : Type u} [AddCommGroup Af] [Module ℂ Af]

/-- The paired cuspidal evaluations embed the finite source tensored with the
original-order infinite standard modules into smooth compact-finite sections. -/
def cuspidalSmoothTensorSection
    (ρ : Representation ℂ Gf Af)
    (ef : Gf → Af →ₗ[ℂ] Vf) (hρ : IsSmooth ρ)
    (hfr : ∀ d g a, ef g (ρ d a) = ef (g * d) a)
    (hfl : HasFiniteScalarCovariance hm P h ef)
    (hf : ∀ (a : Af), (∀ l : Kf, ef l.val a = 0) → a = 0) :
    @CompactTensorSmoothEmbedding F _ _ n B S Af Ai Vf Vi _ _ _ _
      (groupedFiniteCoefficientGroup D) _ _ _ ρ κ ef ei e := by
  let hcov := @cuspidalCompactTensorValue_covariance F _ _ _ r k m hm T P h
    real complex hr hc Af _ _ ef hfl
  have hir (d q : Ki) (b : Ai) : ei q (κ d b) = ei (q * d) b :=
    infiniteEvaluation_right real complex hm T hr hc q d b
  have hi (b : Ai) (hb : ∀ q : Ki, ei q b = 0) : b = 0 := by
    apply infiniteEvaluation_injective real complex hm T hr hc
    funext q
    exact (hb q).trans (map_zero (ei q)).symm
  refine @compactTensorSmoothEmbedding F _ _ n B S Af Ai Vf Vi _ _ _ _
    (groupedFiniteCoefficientGroup D) _ _ _ ρ κ ef ei e hcov hρ hfr hfl hir
    (infiniteStandardAction_isFiniteVector real complex) ?_ hf hi
    (groupedCoefficientEquiv hm P h).injective
  intro a b q l z
  let ℓ : Vi →ₗ[ℂ] ℂ :=
    (groupedCoefficientEvaluation hm P h z).comp (TensorProduct.mk ℂ Vf Vi (ef l.val a))
  let φ := infiniteEvaluationScalarExtension real complex hm T hr hc b ℓ q
  refine ⟨φ.val, φ.property.1, Filter.Eventually.of_forall fun x t ht => ?_⟩
  exact (congrArg φ.val ht.symm).trans (φ.property.2 t)

end Langlands.Global.CuspidalBlockInduction
