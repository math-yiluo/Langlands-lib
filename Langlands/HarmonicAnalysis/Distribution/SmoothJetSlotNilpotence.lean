import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Nilpotence of the action on multilinear jet slots -/

noncomputable section

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k : ℕ}

private def jetSlotMap (A : E →L[ℝ] E) (i : Fin k) : Module.End ℂ (E [×k]→L[ℝ] ℂ) where
  toFun f := f.compContinuousLinearMap (Function.update (fun _ => ContinuousLinearMap.id ℝ E) i A)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem jetSlotMap_apply (A : E →L[ℝ] E) (i : Fin k) (f : E [×k]→L[ℝ] ℂ) (v : Fin k → E) :
    jetSlotMap A i f v = f (Function.update v i (A (v i))) := by
  change f (fun j => (Function.update (fun _ => ContinuousLinearMap.id ℝ E) i A j) (v j)) = _
  congr 1
  funext j
  by_cases hij : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hij]

private theorem jetSlotMap_commute (A : E →L[ℝ] E) (i j : Fin k) :
    Commute (jetSlotMap A i) (jetSlotMap A j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply LinearMap.ext
    intro f
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [Module.End.mul_apply, jetSlotMap_apply, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    congr 1
    funext l
    by_cases hli : l = i
    · subst l
      simp [Function.update_of_ne hij]
    · by_cases hlj : l = j
      · subst l
        simp [Function.update_of_ne (Ne.symm hij)]
      · simp [Function.update_of_ne hli, Function.update_of_ne hlj]

private theorem jetSlotMap_pow_apply (A : E →L[ℝ] E) (i : Fin k) (m : ℕ)
    (f : E [×k]→L[ℝ] ℂ) (v : Fin k → E) :
    (jetSlotMap A i ^ m) f v = f (Function.update v i ((A ^ m) (v i))) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, jetSlotMap_apply, ih, Function.update_self, Function.update_idem]
    rfl

private theorem jetSlotMap_pow_eq_zero (A : E →L[ℝ] E) (i : Fin k) {m : ℕ} (hA : A ^ m = 0) :
    jetSlotMap A i ^ m = 0 := by
  apply LinearMap.ext
  intro f
  apply ContinuousMultilinearMap.ext
  intro v
  rw [jetSlotMap_pow_apply, hA, zero_apply]
  exact f.map_coord_zero i (Function.update_self i 0 v)

/-- The derivation on a multilinear derivative obtained by inserting the vector-field
linearization in each slot in turn. -/
def jetSlotAction (A : E →L[ℝ] E) (k : ℕ) : Module.End ℂ (E [×k]→L[ℝ] ℂ) :=
  ∑ i : Fin k, jetSlotMap A i

@[simp] theorem jetSlotAction_apply (A : E →L[ℝ] E) (k : ℕ) (f : E [×k]→L[ℝ] ℂ) (v : Fin k → E) :
    jetSlotAction A k f v = ∑ i : Fin k, f (Function.update v i (A (v i))) := by
  simp only [jetSlotAction, LinearMap.sum_apply, sum_apply, jetSlotMap_apply]

private theorem jetSlotSum_pow_eq_zero (A : E →L[ℝ] E) {m : ℕ} (hA : A ^ m = 0) (s : Finset (Fin k)) :
    (∑ i ∈ s, jetSlotMap A i) ^ (s.card * m + 1) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    refine (Commute.sum_right _ _ _ (fun j _ => jetSlotMap_commute A i j)).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
      (jetSlotMap_pow_eq_zero A i hA) ih ?_
    rw [Nat.add_mul, one_mul]
    omega

/-- A uniformly nilpotent vector-field linearization induces a uniformly nilpotent
operator on every finite multilinear jet degree, also after scalar multiplication. -/
def SmoothJetSlotNilpotenceStatement : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k m : ℕ)
    (A : E →L[ℝ] E) (c : ℂ), A ^ m = 0 →
      (c • jetSlotAction A k) ^ (k * m + 1) = 0

theorem smoothJetSlotNilpotence : SmoothJetSlotNilpotenceStatement := by
  intro E _ _ k m A c hA
  have h := jetSlotSum_pow_eq_zero A hA (Finset.univ : Finset (Fin k))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change jetSlotAction A k ^ (k * m + 1) = 0 at h
  rw [smul_pow, h, smul_zero]

end Langlands.HarmonicAnalysis
