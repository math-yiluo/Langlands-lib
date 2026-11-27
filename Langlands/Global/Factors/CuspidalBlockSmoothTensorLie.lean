import Langlands.Global.AdelicBlockCoefficientPlaceDifferential
import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluationLie
import Langlands.Global.Factors.CuspidalBlockRegroupedOperators
import Langlands.Global.Factors.CuspidalBlockSectionLieExtension
import Langlands.Global.Factors.CuspidalBlockGroupedFiniteEvaluation

/-! # Lie intertwining of the cuspidal block section map -/

noncomputable section

open scoped BigOperators Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 360000
set_option synthInstance.maxHeartbeats 70000

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic NumberField InfinitePlaceFamily LocalFactor.Archimedean ArchimedeanGL
open ArchimedeanCompactBlocks FiniteAdelicGL GeneralLinear AdelicBlockParabolic
open AdelicBlockScalarSections
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] LocalRealization.localRealizationSpaceAddCommGroup

section ScalarDerivative

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i, OperatorRealization F (B.size i))

local notation "Sections" => smoothCompactFiniteSections F B S
local notation "N" => normalizedCoefficientMap F B S
local notation "Kf" => FiniteAdelicGL.standardIntegral F n

private theorem normalizedCoefficientMap_differential_real_upper
    (v : {v : InfinitePlace F // v.IsReal}) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.IsUpperTriangular) (l : Kf) (f : Sections) :
    N (compactPair F 1 l) (sectionDifferential F B S (realPlaceLieInclusion F n v X) f) =
      archimedeanHalfDerivative F B (realPlaceLieInclusion F n v X) • N (compactPair F 1 l) f +
        coefficientPlaceDifferential F B S (.inl v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i X)
          (N (compactPair F 1 l) f) := by
  let p := parabolicLine ℝ B X hX
  let q (t : ℝ) := realInfiniteParabolicInclusion F B v (p t)
  let Y := realPlaceLieInclusion F n v X
  have hp₀ : p 0 = 1 := parabolicLine_zero ℝ B X hX
  have hq₀ : q 0 = 1 := by
    change realInfiniteParabolicInclusion F B v (p 0) = 1
    rw [hp₀, map_one]
  have hq := realInfiniteParabolicInclusion_hasDerivAt F B v p X (parabolicLine_hasDerivAt ℝ B X hX)
  have hd := normalizedCoefficient_differential_parabolic F B S f l Y q hq₀ hq
    (archimedeanHalfDerivative F B Y) (archimedeanHalfExtension_hasDerivAt F B q hq₀ Y hq)
  rw [coefficientDifferential_realPlace F B S v X] at hd
  exact hd

private theorem normalizedCoefficientMap_differential_complex_upper
    (v : {v : InfinitePlace F // v.IsComplex}) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsUpperTriangular) (l : Kf) (f : Sections) :
    N (compactPair F 1 l) (sectionDifferential F B S (complexPlaceLieInclusion F n v X) f) =
      archimedeanHalfDerivative F B (complexPlaceLieInclusion F n v X) • N (compactPair F 1 l) f +
        coefficientPlaceDifferential F B S (.inr v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i X)
          (N (compactPair F 1 l) f) := by
  let p := parabolicLine ℂ B X hX
  let q (t : ℝ) := complexInfiniteParabolicInclusion F B v (p t)
  let Y := complexPlaceLieInclusion F n v X
  have hp₀ : p 0 = 1 := parabolicLine_zero ℂ B X hX
  have hq₀ : q 0 = 1 := by
    change complexInfiniteParabolicInclusion F B v (p 0) = 1
    rw [hp₀, map_one]
  have hq := complexInfiniteParabolicInclusion_hasDerivAt F B v p X (parabolicLine_hasDerivAt ℂ B X hX)
  have hd := normalizedCoefficient_differential_parabolic F B S f l Y q hq₀ hq
    (archimedeanHalfDerivative F B Y) (archimedeanHalfExtension_hasDerivAt F B q hq₀ Y hq)
  rw [coefficientDifferential_complexPlace F B S v X] at hd
  exact hd

end ScalarDerivative

private theorem identity_of_tensor_evaluations {Af Ai Vf Vi C W : Type*}
    [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup W] [Module ℂ W]
    (J : Af ⊗[ℂ] Ai →ₗ[ℂ] W) (N : W →ₗ[ℂ] C)
    (ef : Af →ₗ[ℂ] Vf) (ei : Ai →ₗ[ℂ] Vi) (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] C)
    (hJ : ∀ a b, N (J (a ⊗ₜ[ℂ] b)) = e (ef a ⊗ₜ[ℂ] ei b))
    (D : Module.End ℂ Ai) (H : Module.End ℂ Vi) (Q : Module.End ℂ C) (R : Module.End ℂ W)
    (c : ℂ) (hD : ∀ b, ei (D b) = c • ei b + H (ei b))
    (hH : ∀ a b, e (a ⊗ₜ[ℂ] H b) = Q (e (a ⊗ₜ[ℂ] b)))
    (hR : ∀ w, N (R w) = c • N w + Q (N w)) (x : Af ⊗[ℂ] Ai) :
    N (J (D.lTensor Af x)) = N (R (J x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [hR, LinearMap.lTensor_tmul, hJ, hJ, hD, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, map_add, map_smul, hH]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem identity_of_coefficient_regrouping {Vf Vi U C : Type*}
    (e : Vf → Vi → C) (L : Vf → Vi → U) (E : U → C)
    (H H' : Vi → Vi) (D : U → U) (Q : C → C)
    (hH : ∀ b, H b = H' b) (hE : ∀ a b, E (L a b) = e a b)
    (hL : ∀ a b, L a (H' b) = D (L a b)) (hQ : ∀ y, Q (E y) = E (D y))
    (a : Vf) (b : Vi) : e a (H b) = Q (e a b) := by
  rw [hH b, ← hE a (H' b), hL, ← hQ, hE]

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
local notation "Sections" => smoothCompactFiniteSections F B S
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
private local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
private local instance : AddCommGroup Sections := Submodule.addCommGroup _

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
local notation "e" => groupedCoefficientEquiv hm P h
local notation "N" => normalizedCoefficientMap F B S
local notation "BlockTensor" => (⨂[ℂ] i, OperatorRealization.Space (S i))

private theorem groupedCoefficientEquiv_infiniteLie (p : Index F) (Y : ∀ i, Lie (m i + 1) p)
    (a : Vf) (b : Vi) :
    e (a ⊗ₜ[ℂ] infiniteCoefficientLieAt T p Y b) =
      coefficientPlaceDifferential F B S p Y (e (a ⊗ₜ[ℂ] b)) := by
  let A (i : Fin k) : Module.End ℂ (CI p i) := (T i).placeDensityModels.sourceLie p (Y i)
  have hsum : placeCoefficientLieSum T p Y = ∑ i, FiniteTensor.slotAlgebraHom i (A i) := by
    unfold placeCoefficientLieSum
    exact Finset.sum_congr rfl fun i _ => (FiniteTensor.slotAlgebraHom_eq_map_ite i A).symm
  have hslot : infiniteCoefficientLieAt T p Y = groupedPlaceOperator p A :=
    congrArg (fun Z : Module.End ℂ (InfinitePlaceCoefficients T p) =>
      (FiniteTensor.slotAlgebraHom p Z : Module.End ℂ Vi)) hsum
  let G := @groupedCoefficientEquiv F _ _ _ r k m hm T P h
  let L := @groupedBlockTensorEquiv F _ _ _ r k m hm T P h
  let E := coefficientEquiv F B S
  let D₀ : Module.End ℂ BlockTensor :=
    ∑ i, FiniteTensor.slotAlgebraHom (V := fun j => (S j).Space) i ((S i).placeLieFamily p (Y i))
  let Q := coefficientPlaceDifferential F B S p Y
  let hE := @coefficientEquiv_groupedBlockTensorEquiv F _ _ _ r k m hm T P h
  let hL := @groupedBlockTensorEquiv_placeLie F _ _ _ r k m hm T P h p Y
  let hQ := coefficientPlaceDifferential_coefficientEquiv F B S p Y
  refine @identity_of_coefficient_regrouping Vf Vi BlockTensor (coefficientValues F B S)
    (fun s t => G (s ⊗ₜ[ℂ] t))
    (fun s t => L (s ⊗ₜ[ℂ] t)) E (infiniteCoefficientLieAt T p Y) (groupedPlaceOperator p A)
    D₀ Q ?_ ?_ ?_ ?_ a b
  · exact LinearMap.congr_fun hslot
  · intro s t
    exact hE (s ⊗ₜ[ℂ] t)
  · exact hL
  · exact hQ

/-- The normalized coefficient formula at infinite compact identity determines
the place Lie comparison for a compact intertwiner on the tensor. -/
def CuspidalSmoothTensorPlaceLieStatement : Prop :=
  ∀ {Af : Type u} [AddCommGroup Af] [Module ℂ Af]
    (ef : Kf → Af →ₗ[ℂ] Vf)
    (J : Representation.IntertwiningMap (V := Af ⊗[ℂ] Ai) (W := ↥Sections)
      (Representation.tprod (Representation.trivial ℂ Ki Af) (infiniteStandardAction r real complex))
      (smoothCompactAction F B S)),
    (∀ (l : Kf) (a : Af) (b : Ai),
      N (compactPair F 1 l) (J (a ⊗ₜ[ℂ] b)) = e (ef l a ⊗ₜ[ℂ] ei 1 b)) →
    ∀ (p : Index F) (X : Lie n p) (x : Af ⊗[ℂ] Ai),
      J (infiniteStandardTensorLie r real complex Af p X x) =
        sectionPlaceLieAction r B S p X (J x)

/-- Differentiation in upper triangular directions gives the same half-character
and block Lie terms on both sides. Compact equivariance gives the remaining directions. -/
theorem cuspidalSmoothTensorSection_intertwines_placeLie :
    CuspidalSmoothTensorPlaceLieStatement hm P h real complex hr hc := by
  intro Af _ _ ef J hJ p X x
  let δ := infiniteStandardTensorLie r real complex Af
  let G := @groupedCoefficientEquiv F _ _ _ r k m hm T P h
  let E := infiniteEvaluation real complex hm T hr hc
  cases p with
  | inl v =>
    refine intertwines_complexification_of_real J.toLinearMap (δ (.inl v))
      (sectionPlaceLieAction r B S (.inl v)) (fun Y y => ?_) X x
    rw [sectionPlaceLieAction_real_one]
    refine sectionLie_real_of_upper r real complex B S J v (fun Z hZ t l => ?_) Y y
    let c := archimedeanHalfDerivative F B (realPlaceLieInclusion F n v Z)
    let A (i : Fin k) : Lie (m i + 1) (.inl v) := 1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i Z
    refine @identity_of_tensor_evaluations Af Ai Vf Vi (coefficientValues F B S) Sections
      _ _ _ _ _ _ _ _ _ _ _ _ J.toLinearMap (N (compactPair F 1 l))
      (ef l) (E 1) G.toLinearMap (hJ l)
      (infiniteStandardLieAt r real complex (.inl v) (1 ⊗ₜ[ℝ] Z))
      (infiniteCoefficientLieAt T (.inl v) A) (coefficientPlaceDifferential F B S (.inl v) A)
      (sectionDifferential F B S (realPlaceLieInclusion F n v Z)) c ?_ ?_ ?_ t
    · exact infiniteEvaluation_lie_real_upper real complex hm T hr hc v Z hZ
    · exact groupedCoefficientEquiv_infiniteLie hm P h (.inl v) A
    · exact normalizedCoefficientMap_differential_real_upper F B S v Z hZ l
  | inr v =>
    refine intertwines_complexification_of_real J.toLinearMap (δ (.inr v))
      (sectionPlaceLieAction r B S (.inr v)) (fun Y y => ?_) X x
    rw [sectionPlaceLieAction_complex_one]
    refine sectionLie_complex_of_upper r real complex B S J v (fun Z hZ t l => ?_) Y y
    let c := archimedeanHalfDerivative F B (complexPlaceLieInclusion F n v Z)
    let A (i : Fin k) : Lie (m i + 1) (.inr v) := 1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i Z
    refine @identity_of_tensor_evaluations Af Ai Vf Vi (coefficientValues F B S) Sections
      _ _ _ _ _ _ _ _ _ _ _ _ J.toLinearMap (N (compactPair F 1 l))
      (ef l) (E 1) G.toLinearMap (hJ l)
      (infiniteStandardLieAt r real complex (.inr v) (1 ⊗ₜ[ℝ] Z))
      (infiniteCoefficientLieAt T (.inr v) A) (coefficientPlaceDifferential F B S (.inr v) A)
      (sectionDifferential F B S (complexPlaceLieInclusion F n v Z)) c ?_ ?_ ?_ t
    · exact infiniteEvaluation_lie_complex_upper real complex hm T hr hc v Z hZ
    · exact groupedCoefficientEquiv_infiniteLie hm P h (.inr v) A
    · exact normalizedCoefficientMap_differential_complex_upper F B S v Z hZ l

end Langlands.Global.CuspidalBlockInduction
