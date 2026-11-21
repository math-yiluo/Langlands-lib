import Langlands.Global.ArchimedeanBlockStandardNormalization
import Langlands.Global.ArchimedeanRealBlockEvaluation
import Langlands.Global.ArchimedeanComplexBlockEvaluation

/-! # Parabolic evaluation of the real and complex standard-module tensors -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean LocalFactor.Archimedean
open GeneralLinear (BlockShape)
open Archimedean.RealLeviChart (pos val_pos blockDiagHom blockDiagGL_val
  blockDiagHom_pos_pos_self blockDiagHom_pos_pos_of_ne)
open Archimedean.RealLeviSlices (flat sz realPositionCharacter_flat start_zero' start_succ')
open AdelicBlockScalarSections (indexedEvaluation indexedEvaluation_tprod)
open AdelicParabolicInduction (orderedBlockShape)

local notation "G" => Langlands.GeneralLinear

section Evaluation

variable {c : ℕ} {V : Fin c → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {X Y : Fin c → Type}

private theorem indexedEvaluation_restrict (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ))
    (j : ∀ i, Y i → X i) (t : ⨂[ℂ] i, V i) (y : ∀ i, Y i) :
    indexedEvaluation e t (fun i => j i (y i)) =
      indexedEvaluation (fun i => (LinearMap.funLeft ℂ ℂ (j i)).comp (e i)) t y := by
  let L := (LinearMap.proj (fun i => j i (y i))).comp (indexedEvaluation e)
  let R := (LinearMap.proj y).comp
    (indexedEvaluation (fun i => (LinearMap.funLeft ℂ ℂ (j i)).comp (e i)))
  have h : L = R := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change indexedEvaluation e (PiTensorProduct.tprod ℂ x) (fun i => j i (y i)) =
      indexedEvaluation (fun i => (LinearMap.funLeft ℂ ℂ (j i)).comp (e i))
        (PiTensorProduct.tprod ℂ x) y
    rw [indexedEvaluation_tprod, indexedEvaluation_tprod]
    rfl
  exact LinearMap.congr_fun h t

end Evaluation

/-- Evaluation maps in the actual block shape, with the normalized local
parabolic formula relating their scalar values to the ambient function. -/
structure StandardBlockEvaluation (𝕜 : Type) [RCLike 𝕜] {n : ℕ} (B : BlockShape n)
    (W : Submodule ℂ (G n 𝕜 → ℂ)) (V : ∀ i, Submodule ℂ (G (B.size i) 𝕜 → ℂ)) where
  evaluation : unitaryCompact 𝕜 n → W →ₗ[ℂ] (⨂[ℂ] i, V i)
  parabolic_value : ∀ (k : unitaryCompact 𝕜 n) (f : W) (p : B.parabolic 𝕜),
    f.val (p.val * k.val) = localLeviHalf 𝕜 B (B.leviProjection 𝕜 p) *
      indexedEvaluation (fun i => (V i).subtype) (evaluation k f) (B.leviProjection 𝕜 p)

section Real

variable {c : ℕ} (ds : Fin c → List RealBlock) (hp : ∀ i, 0 < sz ds i)

local notation "N" => (∑ i, sz ds i)
local notation "B" => orderedBlockShape (sz ds) hp

private theorem realCompactLevi_eq (q : ∀ i, unitaryCompact ℝ (sz ds i)) :
    compactLeviEmbedding ℝ (B) q = realCompactEmbedding ds q := by
  apply Subtype.ext
  apply Units.ext
  refine Matrix.ext fun p r => ?_
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  obtain ⟨⟨j, b⟩, rfl⟩ := finSigmaFinEquiv.surjective r
  change (B).leviEmbedding ℝ (fun i => (q i).val) ((B).index i a) ((B).index j b) =
    blockDiagHom (sz ds) (fun i => (q i).val.val) (pos (sz ds) i a) (pos (sz ds) j b)
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same, blockDiagHom_pos_pos_self]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij, blockDiagHom_pos_pos_of_ne _ _ hij]

/-- The real local parabolic evaluation for the original-order standard function. -/
def realStandardBlockEvaluation :
    StandardBlockEvaluation ℝ (B) (InductionStages.KFin N (flat ds))
      (fun i => InductionStages.KFin (sz ds i) (ds i)) where
  evaluation := realEvaluation ds
  parabolic_value k f p := by
    refine principalSeries_parabolic_tensorValue ℝ (sz ds) hp
      (realPositionCharacter (flat ds)) (fun i => realPositionCharacter (ds i)) ?_
      (fun i => (InductionStages.KFin (sz ds i) (ds i)).subtype)
      (fun _ x => x.2.1.1) f.2.1.1 k.val (realEvaluation ds k f) ?_ p
    · intro i a
      rw [val_pos]
      exact realPositionCharacter_flat ds i a a.isLt
    · intro q
      rw [realCompactLevi_eq ds hp q]
      rw [indexedEvaluation_restrict _ (fun i => Subtype.val (p := (· ∈ unitaryCompact ℝ (sz ds i))))]
      exact realEvaluation_value ds k f q

end Real

section Complex

private theorem complexPositionCharacter_append (a b : List ComplexCharacterData) (j : ℕ) :
    complexPositionCharacter (a ++ b) j =
      if j < a.length then complexPositionCharacter a j else complexPositionCharacter b (j - a.length) := by
  induction a generalizing j with
  | nil => simp
  | cons d a ih =>
      cases j with
      | zero => simp [complexPositionCharacter]
      | succ j =>
        simp only [List.cons_append, complexPositionCharacter, List.length_cons, Nat.succ_lt_succ_iff,
          Nat.succ_sub_succ_eq_sub]
        exact ih j

private theorem complexPositionCharacter_at_block : ∀ {c : ℕ}
    (ds : Fin c → List ComplexCharacterData) (i : Fin c) (a : Fin (ds i).length),
    complexPositionCharacter (List.ofFn ds).flatten (pos (fun j => (ds j).length) i a) =
      complexPositionCharacter (ds i) a
  | 0, _, i, _ => i.elim0
  | c + 1, ds, i, a => by
      rw [List.ofFn_succ, List.flatten_cons, val_pos]
      revert a
      induction i using Fin.cases with
      | zero =>
          intro a
          rw [Fin.val_zero, start_zero', zero_add, complexPositionCharacter_append, ite_eq_left a.isLt]
      | succ i =>
          intro a
          rw [Fin.val_succ, start_succ', add_assoc, complexPositionCharacter_append,
            ite_eq_right (by omega), Nat.add_sub_cancel_left]
          rw [← val_pos (fun j : Fin c => (ds j.succ).length) i a]
          exact complexPositionCharacter_at_block (fun j => ds j.succ) i a

variable {c : ℕ} (ds : Fin c → List ComplexCharacterData) (hp : ∀ i, 0 < (ds i).length)

local notation "szC" => (fun i : Fin c => List.length (ds i))
local notation "N" => (∑ i, szC i)
local notation "B" => orderedBlockShape szC hp
local notation "V" => (fun n d => kFiniteFunctions (complexStandardModule n d) (unitaryCompact ℂ n))

/-- The complex local parabolic evaluation for the original-order standard function. -/
def complexStandardBlockEvaluation :
    StandardBlockEvaluation ℂ (B) (V N (List.ofFn ds).flatten) (fun i => V (szC i) (ds i)) where
  evaluation := complexEvaluation ds hp
  parabolic_value k f p := by
    apply principalSeries_parabolic_tensorValue ℂ szC hp
      (complexPositionCharacter (List.ofFn ds).flatten) (fun i => complexPositionCharacter (ds i))
      (complexPositionCharacter_at_block ds) _ (fun i (x : V (szC i) (ds i)) => x.2.1) f.2.1
    intro q
    rw [indexedEvaluation_restrict _ (fun i => Subtype.val (p := (· ∈ unitaryCompact ℂ (szC i))))]
    exact complexEvaluation_value ds hp k f q

end Complex

/-- Real normalized evaluation in a supplied block shape with the given ranks. -/
def realStandardBlockEvaluationOfShape {n : ℕ} (B : BlockShape n)
    (ds : Fin B.length → List RealBlock) (hr : ∀ i, realRank (ds i) = B.size i) :
    StandardBlockEvaluation ℝ B (InductionStages.KFin n (flat ds))
      (fun i => InductionStages.KFin (B.size i) (ds i)) := by
  obtain ⟨c, size, hp, hs⟩ := B
  change Fin c → List RealBlock at ds
  change ∀ i, realRank (ds i) = size i at hr
  have h : size = sz ds := funext fun i => (hr i).symm
  subst size
  subst n
  exact realStandardBlockEvaluation ds hp

/-- Complex normalized evaluation in a supplied block shape with the given ranks. -/
def complexStandardBlockEvaluationOfShape {n : ℕ} (B : BlockShape n)
    (ds : Fin B.length → List ComplexCharacterData) (hr : ∀ i, (ds i).length = B.size i) :
    StandardBlockEvaluation ℂ B
      (kFiniteFunctions (complexStandardModule n (List.ofFn ds).flatten) (unitaryCompact ℂ n))
      (fun i => kFiniteFunctions (complexStandardModule (B.size i) (ds i)) (unitaryCompact ℂ (B.size i))) := by
  obtain ⟨c, size, hp, hs⟩ := B
  change Fin c → List ComplexCharacterData at ds
  change ∀ i, (ds i).length = size i at hr
  have h : size = fun i => (ds i).length := funext fun i => (hr i).symm
  subst size
  subst n
  exact complexStandardBlockEvaluation ds hp

end Langlands.Global.ArchimedeanCompactBlocks
