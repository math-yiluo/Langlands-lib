import Langlands.Global.Factors.CuspidalBlockCompactCoefficientTranslation
import Langlands.Global.AdelicBlockCompactProduct

/-! # Comparison with the actual smooth compact picture of cuspidal induction -/

noncomputable section

open scoped BigOperators Classical Matrix.Norms.Operator TensorProduct

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
local notation "K" => standardCompact F n
local notation "Ki" => standardInfiniteCompact F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n
local notation "M" => FullLevi F B
local notation "Gf" => FiniteAdelicGL F n
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
private local instance (i : Fin k) : AddCommGroup (BlockInducedReferences.BlockCoefficients D i) :=
  DirectLimit.instAddCommGroupOfAddMonoidHomClass
private local instance (p : Index F) : AddCommGroup (InfinitePlaceCoefficients T p) :=
  PiTensorProduct.instAddCommGroup

local notation "ei" => infiniteEvaluation real complex hm T hr hc
local notation "ev" => groupedCoefficientEvaluation hm P h

variable {Af : Type u} [AddCommGroup Af] [Module ℂ Af]
variable (ef : FiniteAdelicGL F (r + 1) → Af →ₗ[ℂ]
  (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients (finiteReferences hm P) i))


/-- The finite inducing evaluations have normalized parabolic covariance
when paired with any infinite coefficient. -/
def HasFiniteScalarCovariance : Prop :=
  ∀ (p : AdelicBlockParabolic.Finite F B) (g : Gf) (a : Af) (c : Fi) (z : M),
  ev z (ef (p.val * g) a ⊗ₜ[ℂ] c) = (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
    ev (z * leviPair F B 1 (GeneralLinear.BlockShape.leviProjection B (FiniteAdeles F) p))
      (ef g a ⊗ₜ[ℂ] c)

omit [CompactSpace (AdeleQuotient F)] in
private theorem halfCharacter_finiteCompact (p : finiteCompactIntersection F B) :
    parabolicHalfCharacter F B (ofFinite F B p.val) = 1 :=
  parabolicHalfCharacter_eq_one_of_mem_standardCompact B F (ofFinite F B p.val)
    (compactPair F (1 : Ki) (⟨p.val.val, p.property⟩ : Kf)).property

private theorem scalarEvaluation_left
    (hl : HasFiniteScalarCovariance hm P h ef)
    (p : infiniteCompactIntersection F B) (l : finiteCompactIntersection F B)
    (q : Ki) (g : Kf) (z : M) (a : Af) (b : InfiniteStandardTensor) :
    ev z (ef (l.val.val * g.val) a ⊗ₜ[ℂ] ei (⟨p.val.val, p.property⟩ * q) b) =
      ev (z * leviPair F B (GeneralLinear.BlockShape.leviProjection B (InfiniteAdeles F) p.val)
        (GeneralLinear.BlockShape.leviProjection B (FiniteAdeles F) l.val))
        (ef g.val a ⊗ₜ[ℂ] ei q b) := by
  let d := infiniteLeviCompact B p
  let j : InfiniteLevi F B := fun i => (d i).val
  let μ : FiniteLevi F B := GeneralLinear.BlockShape.leviProjection B (FiniteAdeles F) l.val
  let a' : Ff := ef (l.val.val * g.val) a
  let b' : Fi := ei q b
  have hmul : leviPair F B j 1 * leviPair F B 1 μ = leviPair F B j μ := by
    funext i
    change AdelicGL.pair F (m i + 1) (j i) 1 * AdelicGL.pair F (m i + 1) 1 (μ i) = _
    rw [AdelicGL.pair_mul, mul_one, one_mul]
    rfl
  calc
    _ = ev z (a' ⊗ₜ[ℂ] infiniteCoefficientCompactMap T d b') :=
      congrArg (fun v : Fi => ev z (a' ⊗ₜ[ℂ] v))
        (infiniteEvaluation_left T hm real complex hr hc p q b)
    _ = ev (z * leviPair F B j 1) (a' ⊗ₜ[ℂ] b') :=
      groupedCoefficientEquiv_compact hm P h d a' b' z
    _ = ev ((z * leviPair F B j 1) * leviPair F B 1 μ) (ef g.val a ⊗ₜ[ℂ] b') := by
      let y := ev ((z * leviPair F B j 1) * leviPair F B 1 μ) (ef g.val a ⊗ₜ[ℂ] b')
      have he : ev (z * leviPair F B j 1) (a' ⊗ₜ[ℂ] b') =
          (parabolicHalfCharacter F B (ofFinite F B l.val) : ℂ) * y :=
        hl l.val g.val a b' (z * leviPair F B j 1)
      calc
        _ = (parabolicHalfCharacter F B (ofFinite F B l.val) : ℂ) * y := he
        _ = 1 * y := congrArg (fun c : ℂˣ => (c : ℂ) * y) (halfCharacter_finiteCompact hm l)
        _ = y := one_mul y
    _ = _ :=
      congrArg (fun w : M => ev w (ef g.val a ⊗ₜ[ℂ] b'))
        ((mul_assoc z _ _).trans (congrArg (z * ·) hmul))


/-- Scalar compact evaluation transforms by the Levi projection of each
compact parabolic element. -/
theorem compactEvaluation_left
    (hl : HasFiniteScalarCovariance hm P h ef)
    (p : compactIntersection B F) (q : K) (z : M) (a : Af) (b : InfiniteStandardTensor) :
    let x := standardCompactProductEquiv F n (⟨p.val.val, p.property⟩ * q)
    let y := standardCompactProductEquiv F n q
    ev z (ef x.2.val a ⊗ₜ[ℂ] ei x.1 b) =
      ev (z * GeneralLinear.BlockShape.leviProjection B (Adeles F) p.val)
        (ef y.2.val a ⊗ₜ[ℂ] ei y.1 b) := by
  let U := standardCompactProductEquiv F n
  let q' := U q
  let p' := compactIntersectionProductEquiv F B p
  let pInf : Ki := ⟨p'.1.val.val, p'.1.property⟩
  let pFin : Kf := ⟨p'.2.val.val, p'.2.property⟩
  let qp : K := ⟨p.val.val, p.property⟩
  have hparts : U qp = (pInf, pFin) := standardCompactProductEquiv_compactIntersection F B p
  have hcoords : U (qp * q) = ((pInf, pFin) : Ki × Kf) * q' := by
    calc
      U (qp * q) = U qp * q' := U.map_mul qp q
      _ = ((pInf, pFin) : Ki × Kf) * q' := congrArg (fun x : Ki × Kf => x * q') hparts
  let j : InfiniteLevi F B := GeneralLinear.BlockShape.leviProjection B (InfiniteAdeles F) p'.1.val
  let l : FiniteLevi F B := GeneralLinear.BlockShape.leviProjection B (FiniteAdeles F) p'.2.val
  have hprojection : GeneralLinear.BlockShape.leviProjection B (Adeles F) p.val = leviPair F B j l := by
    have hp := congrArg (fun t : compactIntersection B F => t.val)
      ((compactIntersectionProductEquiv F B).symm_apply_apply p)
    change AdelicBlockParabolic.pair F B p'.1.val p'.2.val = p.val at hp
    exact (congrArg (GeneralLinear.BlockShape.leviProjection B (Adeles F)) hp).symm.trans
      (leviProjection_pair F B p'.1.val p'.2.val)
  let value (t : Ki × Kf) (w : M) := ev w (ef t.2.val a ⊗ₜ[ℂ] ei t.1 b)
  calc
    value (U (qp * q)) z = value (((pInf, pFin) : Ki × Kf) * q') z := congrArg (fun t => value t z) hcoords
    _ = value q' (z * leviPair F B j l) :=
      scalarEvaluation_left hm P h real complex hr hc ef hl p'.1 p'.2 q'.1 q'.2 z a b
    _ = _ := congrArg (fun t : M => value q' (z * t)) hprojection.symm


end Langlands.Global.CuspidalBlockInduction
