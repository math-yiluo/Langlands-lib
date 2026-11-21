import Langlands.Automorphic.FiniteInfiniteMultiplicity
import Langlands.Global.AdelicBlockCoefficientDifferential
import Langlands.Representation.Tensor.TensorProductInterchange

/-! # Grouping the actual finite and infinite Levi coefficients -/

noncomputable section

open NumberField
open scoped Classical BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic
open Langlands.GeneralLinear (BlockShape)
open AdelicBlockParabolic ArchimedeanGL PrimitiveAdelicHeight AdelicBlockDeterminantCharacter

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local instance groupedCoeffRationalGroup (t : ℕ) :
    AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance groupedCoeffContinuousGroup (t : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance groupedCoeffSmoothGroup (t : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F t) := Submodule.addCommGroup _
local instance groupedCoeffFormsGroup (t : ℕ) :
    AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance groupedCoeffStableGroup (t : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance groupedCoeffOperatorGroup {t : ℕ} (P : OperatorRealization F t) :
    AddCommGroup P.Space := Submodule.addCommGroup _

variable (M : ∀ i, Subrepresentation (S i).finiteRepresentation)

local instance groupedCoeffFiniteGroup (i : Fin B.length) :
    AddCommGroup (M i).toSubmodule := Submodule.addCommGroup _

local notation "V" => fun i : Fin B.length => Subrepresentation.toSubmodule (M i)
local notation "U" => fun i : Fin B.length => OperatorRealization.FiniteMultiplicity (S i) (M i)
local notation "Vf" => (⨂[ℂ] i, V i)
local notation "Vi" => (⨂[ℂ] i, U i)
local notation "W" => coefficientValues F B S
local notation "A" => ArchimedeanMatrix F n
local notation "eval" => fun i : Fin B.length => OperatorRealization.finiteMultiplicityEvaluation (S i) (M i)

/-- Evaluate the grouped finite and infinite inducing tensors in the actual
scalar Levi coefficient space. -/
def groupedMultiplicityCoefficients : Vf ⊗[ℂ] Vi →ₗ[ℂ] W :=
  (coefficientEquiv F B S).toLinearMap.comp
    ((PiTensorProduct.map eval).comp (FiniteTensor.pairTensorEquiv V U).toLinearMap)

/-- The inducing multiplicity equivalences identify the grouped model with
the entire actual coefficient space. -/
theorem groupedMultiplicityCoefficients_bijective
    (hS : ∀ i, (S i).IsIrreducible) (hm : ∀ i, M i ≠ ⊥)
    (hI : ∀ i, (M i).toRepresentation.IsIrreducible) (hA : ∀ i, IsAdmissible (M i).toRepresentation) :
    Function.Bijective (groupedMultiplicityCoefficients F B S M) := by
  let e (i : Fin B.length) := (S i).finiteMultiplicityEquiv (M i) (hS i) (hm i) (hI i) (hA i)
  exact ((FiniteTensor.pairTensorEquiv V U).trans
    ((PiTensorProduct.congr e).trans (coefficientEquiv F B S))).bijective

set_option backward.isDefEq.respectTransparency true in
private theorem groupedMultiplicityCoefficients_map
    (a : ∀ i, V i →ₗ[ℂ] V i) (b : ∀ i, U i →ₗ[ℂ] U i)
    (d : ∀ i, Module.End ℂ (S i).Space)
    (h : ∀ i t, eval i (TensorProduct.map (a i) (b i) t) = d i (eval i t))
    (t : Vf ⊗[ℂ] Vi) :
    groupedMultiplicityCoefficients F B S M (TensorProduct.map (PiTensorProduct.map a) (PiTensorProduct.map b) t) =
      (coefficientEquiv F B S) (PiTensorProduct.map d
        ((coefficientEquiv F B S).symm (groupedMultiplicityCoefficients F B S M t))) := by
  let e := coefficientEquiv F B S
  let p := FiniteTensor.pairTensorEquiv (𝕜 := ℂ) V U
  let a' := TensorProduct.map (PiTensorProduct.map a) (PiTensorProduct.map b)
  let b' (i : Fin B.length) : Module.End ℂ (V i ⊗[ℂ] U i) := TensorProduct.map (a i) (b i)
  let p' := PiTensorProduct.map b'
  let q := PiTensorProduct.map eval
  let d' := PiTensorProduct.map d
  have hp : p (a' t) = p' (p t) := FiniteTensor.pairTensorEquiv_map a b t
  have he (z : ⨂[ℂ] i, V i ⊗[ℂ] U i) : q (p' z) = d' (q z) := by
    change (q.comp p') z = (d'.comp q) z
    have hh : (fun i => (eval i).comp (b' i)) = fun i => (d i).comp (eval i) :=
      funext fun i => LinearMap.ext (h i)
    have hq : q.comp p' = d'.comp q := calc
      q.comp p' = PiTensorProduct.map (fun i => (eval i).comp (b' i)) :=
        (PiTensorProduct.map_comp eval b').symm
      _ = PiTensorProduct.map (fun i => (d i).comp (eval i)) := congrArg PiTensorProduct.map hh
      _ = d'.comp q := PiTensorProduct.map_comp d eval
    exact LinearMap.congr_fun hq z
  change e (q (p (a' t))) = e (d' (e.symm (e (q (p t)))))
  calc
    e (q (p (a' t))) = e (q (p' (p t))) := congrArg (fun z => e (q z)) hp
    _ = e (d' (q (p t))) := congrArg e (he (p t))
    _ = e (d' (e.symm (e (q (p t))))) := congrArg (fun z => e (d' z)) (e.symm_apply_apply _).symm

private abbrev blockGenerator (i : Fin B.length) (X : A) :=
  envelopingGenerator F (B.size i) (complexify F (B.size i)
    ((realLieAlgebraToMatrix F (B.size i)).symm (archimedeanDiagonalBlock F B i X)))

/-- The projected real Lie direction differentiates only the infinite
multiplicity tensor, one Levi block at a time. -/
def infiniteMultiplicityDifferential (X : A) : Module.End ℂ Vi :=
  ∑ i, PiTensorProduct.map (fun j => if j = i then
    (S j).finiteMultiplicityEnveloping (M j) (blockGenerator F B j X) else LinearMap.id)

set_option backward.isDefEq.respectTransparency true in
/-- The actual differential of a Levi coefficient acts on the infinite
multiplicity tensor and leaves its finite tensor factor fixed. -/
theorem groupedMultiplicityCoefficients_differential (X : A) (t : Vf ⊗[ℂ] Vi) :
    coefficientDifferential F B S X (groupedMultiplicityCoefficients F B S M t) =
      groupedMultiplicityCoefficients F B S M ((infiniteMultiplicityDifferential F B S M X).lTensor Vf t) := by
  let e := coefficientEquiv F B S
  let a (i j : Fin B.length) : Module.End ℂ (U j) :=
    if j = i then (S j).finiteMultiplicityEnveloping (M j) (blockGenerator F B j X) else LinearMap.id
  let b (i j : Fin B.length) : Module.End ℂ (S j).Space :=
    if j = i then (S j).envelopingAction (blockGenerator F B j X) else LinearMap.id
  let c := groupedMultiplicityCoefficients F B S M
  let ai (i : Fin B.length) : Module.End ℂ Vi := PiTensorProduct.map (a i)
  let bi (i : Fin B.length) : Module.End ℂ (⨂[ℂ] j, (S j).Space) := PiTensorProduct.map (b i)
  have h (i : Fin B.length) : c ((ai i).lTensor Vf t) = e (bi i (e.symm (c t))) := by
    have hslot (j : Fin B.length) (z : V j ⊗[ℂ] U j) :
        eval j (TensorProduct.map LinearMap.id (a i j) z) = b i j (eval j z) := by
      by_cases hij : j = i
      · simpa only [a, b, ite_eq_left hij] using
          (S j).finiteMultiplicityEvaluation_enveloping (M j) (blockGenerator F B j X) z
      · simp only [a, b, ite_eq_right hij, TensorProduct.map_id, LinearMap.id_apply]
    have hmap := groupedMultiplicityCoefficients_map F B S M (fun _ => LinearMap.id)
      (a i) (b i) hslot t
    simpa only [PiTensorProduct.map_id, c, ai, bi, e, LinearMap.lTensor_def] using hmap
  let lift : Module.End ℂ Vi →ₗ[ℂ] Module.End ℂ (Vf ⊗[ℂ] Vi) := LinearMap.lTensorHom Vf
  change e ((∑ i, bi i) (e.symm (c t))) = c (lift (∑ i, ai i) t)
  calc
    e ((∑ i, bi i) (e.symm (c t))) = ∑ i, e (bi i (e.symm (c t))) := by
      simp only [LinearMap.sum_apply, map_sum]
    _ = ∑ i, c (lift (ai i) t) := Finset.sum_congr rfl (fun i _ => (h i).symm)
    _ = c (lift (∑ i, ai i) t) := by simp only [map_sum, LinearMap.sum_apply]

set_option backward.isDefEq.respectTransparency true in
/-- Finite Levi translation acts in the first factor of the grouped coefficients. -/
theorem groupedMultiplicityCoefficients_finite (d : FiniteLevi F B) (t : Vf ⊗[ℂ] Vi)
    (m : FullLevi F B) :
    (groupedMultiplicityCoefficients F B S M
      ((PiTensorProduct.map (fun i => (M i).toRepresentation (d i))).rTensor Vi t)).val m =
      (groupedMultiplicityCoefficients F B S M t).val (m * leviPair F B 1 d) := by
  let c := groupedMultiplicityCoefficients F B S M
  let a (i : Fin B.length) : Module.End ℂ (V i) := (M i).toRepresentation (d i)
  let b (i : Fin B.length) : Module.End ℂ (S i).Space := (S i).finiteRepresentation (d i)
  let e := coefficientEquiv F B S
  have h : c ((PiTensorProduct.map a).rTensor Vi t) =
      e (PiTensorProduct.map b (e.symm (c t))) := by
    simpa only [PiTensorProduct.map_id, LinearMap.rTensor_def, c, e] using
      groupedMultiplicityCoefficients_map F B S M a (fun _ => LinearMap.id) b
        (fun i => (S i).finiteMultiplicityEvaluation_finite (M i) (d i)) t
  calc
    (c ((PiTensorProduct.map a).rTensor Vi t)).val m =
        (e (PiTensorProduct.map b (e.symm (c t)))).val m := congrArg (fun v : W => v.val m) h
    _ = (e (e.symm (c t))).val (m * leviPair F B 1 d) :=
      coefficientEvaluation_finite F B S d (e.symm (c t)) m
    _ = (c t).val (m * leviPair F B 1 d) := congrArg (fun v : W => v.val _) (e.apply_symm_apply _)

set_option backward.isDefEq.respectTransparency true in
/-- Infinite compact Levi translation acts in the second factor of the grouped coefficients. -/
theorem groupedMultiplicityCoefficients_compact
    (k : ∀ i, standardInfiniteCompact F (B.size i)) (t : Vf ⊗[ℂ] Vi)
    (m : FullLevi F B) :
    (groupedMultiplicityCoefficients F B S M
      ((PiTensorProduct.map (fun i => (S i).finiteMultiplicityCompact (M i) (k i))).lTensor Vf t)).val m =
      (groupedMultiplicityCoefficients F B S M t).val (m * leviPair F B (fun i => (k i).val) 1) := by
  let c := groupedMultiplicityCoefficients F B S M
  let a (i : Fin B.length) : Module.End ℂ (U i) := (S i).finiteMultiplicityCompact (M i) (k i)
  let b (i : Fin B.length) : Module.End ℂ (S i).Space := (S i).compactRepresentation (k i)
  let e := coefficientEquiv F B S
  have h : c ((PiTensorProduct.map a).lTensor Vf t) =
      e (PiTensorProduct.map b (e.symm (c t))) := by
    simpa only [PiTensorProduct.map_id, LinearMap.lTensor_def, c, e] using
      groupedMultiplicityCoefficients_map F B S M (fun _ => LinearMap.id) a b
        (fun i => (S i).finiteMultiplicityEvaluation_compact (M i) (k i)) t
  calc
    (c ((PiTensorProduct.map a).lTensor Vf t)).val m =
        (e (PiTensorProduct.map b (e.symm (c t)))).val m := congrArg (fun v : W => v.val m) h
    _ = (e (e.symm (c t))).val (m * leviPair F B (fun i => (k i).val) 1) :=
      coefficientEvaluation_compact F B S k (e.symm (c t)) m
    _ = (c t).val (m * leviPair F B (fun i => (k i).val) 1) :=
      congrArg (fun v : W => v.val _) (e.apply_symm_apply _)

end Langlands.Global.AdelicBlockScalarSections
