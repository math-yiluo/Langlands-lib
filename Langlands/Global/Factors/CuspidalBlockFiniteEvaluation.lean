import Langlands.Automorphic.CuspidalPresentationTensorDecomposition
import Langlands.Global.Factors.CuspidalBlockInductionReferences
import Langlands.Global.FiniteAdelicGL.BlockEvaluationRegrouping

/-! # Evaluation in the actual cuspidal finite Levi factors -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic FiniteAdelicGL GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

private theorem transport_covariance
    {L X Y : Type u} [Monoid L]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ L X} {τ : Representation ℂ L Y}
    (j : ρ.IntertwiningMap τ) (d : L) (c : ℂ) {x y : X}
    (h : x = c • ρ d y) : j x = c • τ d (j y) := by
  change j.toLinearMap x = c • τ d (j.toLinearMap y)
  rw [h, map_smul]
  exact congrArg (c • ·) (j.isIntertwining _ _ d y)

/-- Finite inducing evaluation together with its translation laws and compact separation. -/
structure FiniteEvaluationData {G L P K A W : Type u}
    [Monoid G] [Monoid L] [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G A) (τ : Representation ℂ L W)
    (leftTranslate : P → G → G) (character : P → ℂ) (levi : P → L) (compact : K → G) where
  evaluate : G → A →ₗ[ℂ] W
  right : ∀ d g a, evaluate g (ρ d a) = evaluate (g * d) a
  parabolic : ∀ p g a, evaluate (leftTranslate p g) a = character p • τ (levi p) (evaluate g a)
  compact_injective : Function.Injective (fun a : A => fun l : K => evaluate (compact l) a)

section Transport

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {B : BlockShape n}
variable {V : FinitePlace F → Fin B.length → Type u}
variable [∀ v i, AddCommGroup (V v i)] [∀ v i, Module ℂ (V v i)]
variable {σ : ∀ v i, Representation ℂ (FiniteLocalGL F (B.size i) v) (V v i)}
variable (D : BlockInducedReferences F B σ)
variable (hD : ∀ w ∉ D.exceptional, ∀ i, D.blockReference w i ≠ 0)
variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ (FiniteLevi F B) W}

private def composedEvaluation
    (j : (FiniteTensor.external D.blockRepresentation).IntertwiningMap τ)
    (hj : Function.Injective j) :
    FiniteEvaluationData D.sourceRepresentation τ
      (fun (p : AdelicBlockParabolic.Finite F B) g => p.val * g)
      (fun p => parabolicHalfCharacter F B (ofFinite F B p))
      (B.leviProjection (FiniteAdeles F)) (fun l : FiniteAdelicGL.standardIntegral F n => l.val) where
  evaluate g := j.toLinearMap.comp (D.blockEvaluation hD g)
  right d g a := congrArg j (D.blockEvaluation_right hD d g a)
  parabolic p g a := transport_covariance j (B.leviProjection (FiniteAdeles F) p)
    (parabolicHalfCharacter F B (ofFinite F B p) : ℂ)
    (x := D.blockEvaluation hD (p.val * g) a) (y := D.blockEvaluation hD g a)
    (D.blockEvaluation_parabolic hD p g a)
  compact_injective := by
    intro a b he
    apply D.blockEvaluation_compact_injective hD
    funext l
    exact hj (congrFun he l)

end Transport

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

local notation "B" => blockShape hm
local notation "D" => finiteReferences hm P

/-- Use the actual finite factors in the finite–infinite decompositions of the blocks. -/
def inducingFiniteFactor (T : ∀ i, CuspidalOperatorRealization F (m i)) (i : Fin k) :=
  (T i).finiteInfiniteDecomposition.finite

attribute [local instance] LocalRealization.localRealizationSpaceAddCommGroup
  CuspidalOperatorRealization.FiniteInfiniteDecomposition.cuspidalFiniteInfiniteFactorGroup

set_option quotPrecheck false in
local notation "V" => fun i : Fin k => (T i).finiteInfiniteDecomposition.finite.toSubmodule
local notation "Vf" => (⨂[ℂ] i, V i)

variable (T) in
/-- The actual finite Levi acts on the tensor of the chosen cuspidal finite factors. -/
def inducingFiniteLeviRepresentation : Representation ℂ (FiniteLevi F B) Vf :=
  FiniteTensor.external (fun i => (T i).finiteInfiniteDecomposition.finite.toRepresentation)

private def finiteBlockEquiv (i : Fin k) :
    ((D).blockRepresentation i).Equiv (T i).finiteInfiniteDecomposition.finite.toRepresentation :=
  (blockTensorPresentationEquiv hm P i).trans ((P i).finiteTensorEquiv (h i))

private def finiteCoefficientIntertwiner :
    (FiniteTensor.external (D).blockRepresentation).IntertwiningMap
      (inducingFiniteLeviRepresentation hm T) :=
  FiniteTensor.externalMap (fun i => (finiteBlockEquiv hm P h i).toIntertwiningMap)

private theorem finiteCoefficientIntertwiner_injective :
    Function.Injective (finiteCoefficientIntertwiner hm P h) := by
  let E := PiTensorProduct.congr (fun i => (finiteBlockEquiv hm P h i).toLinearEquiv)
  exact E.injective

/-- Evaluate the exact finite inducing tensor in the finite factors of the actual blocks. -/
def realizedFiniteEvaluation :=
  composedEvaluation (D) (finiteReferences_blockReference_ne_zero hm P)
    (finiteCoefficientIntertwiner hm P h) (finiteCoefficientIntertwiner_injective hm P h)

end Langlands.Global.CuspidalBlockInduction
