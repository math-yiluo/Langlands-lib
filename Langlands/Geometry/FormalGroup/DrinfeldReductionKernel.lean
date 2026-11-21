import Langlands.Geometry.FormalGroup.DrinfeldFixedPointLifting
import Langlands.Geometry.FormalGroup.DrinfeldFixedPointOperator
import Mathlib.Algebra.BigOperators.Fin

/-! # Kernel representatives for reduction of the modified Dieudonné module -/

noncomputable section

namespace Langlands.FormalGroup.Drinfeld.ModifiedModule

variable {O M M' : Type*} [CommRing O] [AddCommGroup M] [AddCommGroup M']
  [Module O M] [Module O M']
variable (n : ℕ) (V P : Module.End O M) {V' P' : Module.End O M'} (f : M →ₗ[O] M')

@[simp]
theorem map_slot (hV : ∀ x, f (V x) = V' (f x)) (hP : ∀ x, f (P x) = P' (f x))
    (i : Fin (n + 1)) (x : M) :
    map n V P f hV hP (slot n V P i x) = slot n V' P' i (f x) := by
  change map n V P f hV hP ((modifiedRelations n V P).mkQ (Pi.single i x)) =
    (modifiedRelations n V' P').mkQ (Pi.single i (f x))
  rw [map_mkQ]
  apply congrArg (modifiedRelations n V' P').mkQ
  funext j
  exact LinearMap.apply_single (fun _ : Fin (n + 1) => f) i j x

private theorem map_modifiedRelations (hV : ∀ x, f (V x) = V' (f x)) (hP : ∀ x, f (P x) = P' (f x))
    (hf : Function.Surjective f) :
    (modifiedRelations n V P).map (f.compLeft (Fin (n + 1))) = modifiedRelations n V' P' := by
  have h (i : Fin n) :
      (LinearMap.range (adjacentRelation n V P i)).map (f.compLeft (Fin (n + 1))) =
        LinearMap.range (adjacentRelation n V' P' i) := by
    have hcomp : (f.compLeft (Fin (n + 1))).comp (adjacentRelation n V P i) =
        (adjacentRelation n V' P' i).comp f := by
      apply LinearMap.ext
      intro x
      funext j
      change f ((Pi.single i.castSucc (V x) : Fin (n + 1) → M) j -
          (Pi.single i.succ (P x) : Fin (n + 1) → M) j) =
        (Pi.single i.castSucc (V' (f x)) : Fin (n + 1) → M') j -
          (Pi.single i.succ (P' (f x)) : Fin (n + 1) → M') j
      rw [map_sub, LinearMap.apply_single (fun _ : Fin (n + 1) => f),
        LinearMap.apply_single (fun _ : Fin (n + 1) => f), hV, hP]
    rw [← LinearMap.range_comp, hcomp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hf)]
  simp only [modifiedRelations, Submodule.map_iSup, h]

/-- A kernel class of the modified map has a representative in the original kernel in every slot. -/
theorem exists_kernel_tuple (hV : ∀ x, f (V x) = V' (f x)) (hP : ∀ x, f (P x) = P' (f x))
    (hf : Function.Surjective f) (z : ModifiedModule n V P) (hz : map n V P f hV hP z = 0) :
    ∃ x : Fin (n + 1) → M, (∀ i, f (x i) = 0) ∧ (modifiedRelations n V P).mkQ x = z := by
  obtain ⟨x, rfl⟩ := (modifiedRelations n V P).mkQ_surjective z
  let g := f.compLeft (Fin (n + 1))
  have h : g x ∈ (modifiedRelations n V P).map g := by
    rw [map_modifiedRelations n V P f hV hP hf, ← (modifiedRelations n V' P').ker_mkQ,
      LinearMap.mem_ker]
    exact hz
  obtain ⟨y, hy, hxy⟩ := h
  refine ⟨x - y, ?_, ?_⟩
  · intro i
    change g (x - y) i = 0
    rw [map_sub, hxy, sub_self]
    rfl
  · have hyq : (modifiedRelations n V P).mkQ y = 0 := by
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ]
    rw [map_sub, hyq, sub_zero]

section FixedPointOperator

omit [AddCommGroup M'] [Module O M'] in
private theorem fixedPointOperator_slot_zero (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x)) (x : M) :
    fixedPointOperator n V P L hL (slot n V P 0 x) = L x := by
  change fixedPointOperator n V P L hL ((modifiedRelations n V P).mkQ (Pi.single 0 x)) = L x
  rw [fixedPointOperator_mkQ, Pi.single_eq_same]
  have hshift : Fin.lastCases (motive := fun _ => M) 0
      (fun i : Fin n => (Pi.single 0 x : Fin (n + 1) → M) i.succ) = 0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  rw [hshift, map_zero, add_zero]

omit [AddCommGroup M'] [Module O M'] in
private theorem fixedPointOperator_slot_succ (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x)) (i : Fin n) (x : M) :
    fixedPointOperator n V P L hL (slot n V P i.succ x) = slot n V P i.castSucc x := by
  change fixedPointOperator n V P L hL ((modifiedRelations n V P).mkQ (Pi.single i.succ x)) =
    (modifiedRelations n V P).mkQ (Pi.single i.castSucc x)
  rw [fixedPointOperator_mkQ, Pi.single_eq_of_ne i.succ_ne_zero.symm, map_zero, zero_add]
  apply congrArg (modifiedRelations n V P).mkQ
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp only [Fin.lastCases_castSucc]
    by_cases he : k = i
    · subst k
      simp
    · rw [Pi.single_eq_of_ne (fun e => he (Fin.succ_injective _ e)),
        Pi.single_eq_of_ne (fun e => he (Fin.castSucc_injective _ e))]

/-- The uniformizer acts coordinatewise on the modified quotient. -/
def uniformizerAction (hcomm : Commute P V) : Module.End O (ModifiedModule n V P) :=
  map n V P P (fun x => LinearMap.congr_fun hcomm.eq x) (fun _ => rfl)

/-- The fixed-point operator is nilpotent on the reduction kernel if the uniformizer's
cycle power kills the original kernel and the lift adds a uniformizer factor there. -/
theorem fixedPointOperator_pow_of_map_eq_zero
    (hV : ∀ x, f (V x) = V' (f x)) (hP : ∀ x, f (P x) = P' (f x)) (hf : Function.Surjective f)
    (hcomm : Commute P V) (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x))
    (hLcomm : L.comp P = (uniformizerAction n V P hcomm).comp L)
    (hkill : ∀ x, f x = 0 → (P ^ (n + 1)) x = 0)
    (hLker : ∀ x, f x = 0 → ∃ y, f y = 0 ∧ L x = slot n V P 0 (P y))
    (z : ModifiedModule n V P) (hz : map n V P f hV hP z = 0) :
    (fixedPointOperator n V P L hL ^ (2 * n + 1)) z = 0 := by
  let Φ := fixedPointOperator n V P L hL
  let A := uniformizerAction n V P hcomm
  have hLpow (k : ℕ) (x : M) : L ((P ^ k) x) = (A ^ k) (L x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, show L (P ((P ^ k) x)) = A (L ((P ^ k) x)) from
        LinearMap.congr_fun hLcomm ((P ^ k) x), ih, pow_succ', Module.End.mul_apply]
  have hslotpow (k : ℕ) (x : M) : (A ^ k) (slot n V P 0 x) = slot n V P 0 ((P ^ k) x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      exact map_slot n V P P _ _ 0 _
  have hfirst (k : ℕ) (x : M) (hx : f x = 0) :
      ∃ y, f y = 0 ∧ (Φ ^ k) (slot n V P 0 x) = slot n V P 0 ((P ^ k) y) := by
    induction k with
    | zero => exact ⟨x, hx, by simp⟩
    | succ k ih =>
      obtain ⟨y, hy, hslot⟩ := ih
      obtain ⟨t, ht, hLt⟩ := hLker y hy
      refine ⟨t, ht, ?_⟩
      rw [pow_succ', Module.End.mul_apply, hslot]
      change fixedPointOperator n V P L hL (slot n V P 0 ((P ^ k) y)) = _
      rw [fixedPointOperator_slot_zero, hLpow, hLt, hslotpow, pow_succ, Module.End.mul_apply]
  have hfirst_zero (x : M) (hx : f x = 0) : (Φ ^ (n + 1)) (slot n V P 0 x) = 0 := by
    obtain ⟨y, hy, hslot⟩ := hfirst (n + 1) x hx
    rw [hslot, hkill y hy, map_zero]
  have hshift (x : M) (k : ℕ) (hk : k < n + 1) :
      (Φ ^ k) (slot n V P ⟨k, hk⟩ x) = slot n V P 0 x := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt : k < n := by omega
      let i : Fin n := ⟨k, hlt⟩
      rw [pow_succ, Module.End.mul_apply]
      change (Φ ^ k) (fixedPointOperator n V P L hL (slot n V P i.succ x)) = _
      rw [fixedPointOperator_slot_succ]
      exact ih _
  have hslot_zero (i : Fin (n + 1)) (x : M) (hx : f x = 0) :
      (Φ ^ (2 * n + 1)) (slot n V P i x) = 0 := by
    have hexp : 2 * n + 1 = (n - i.val) + (n + 1) + i.val := by have hi := i.isLt; omega
    rw [hexp, pow_add, pow_add, Module.End.mul_apply, Module.End.mul_apply,
      hshift x i.val i.isLt, hfirst_zero x hx, map_zero]
  obtain ⟨x, hx, rfl⟩ := exists_kernel_tuple n V P f hV hP hf z hz
  have hsum : (modifiedRelations n V P).mkQ x = ∑ i, slot n V P i (x i) := by
    simp only [slot, LinearMap.comp_apply, LinearMap.single_apply, ← map_sum, Finset.univ_sum_single]
  change (Φ ^ (2 * n + 1)) ((modifiedRelations n V P).mkQ x) = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => hslot_zero i (x i) (hx i)

/-- Under the kernel conditions, reduction identifies the fixed submodules. -/
def fixedPointReductionEquiv
    (hV : ∀ x, f (V x) = V' (f x)) (hP : ∀ x, f (P x) = P' (f x)) (hf : Function.Surjective f)
    (hcomm : Commute P V) (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x))
    (hLcomm : L.comp P = (uniformizerAction n V P hcomm).comp L)
    (hkill : ∀ x, f x = 0 → (P ^ (n + 1)) x = 0)
    (hLker : ∀ x, f x = 0 → ∃ y, f y = 0 ∧ L x = slot n V P 0 (P y))
    (L' : M' →ₗ[O] ModifiedModule n V' P') (hL' : ∀ x, L' (V' x) = slot n V' P' 0 (P' x))
    (hmap : ∀ x, map n V P f hV hP (L x) = L' (f x)) :
    (fixedPointOperator n V P L hL).fixedSubmodule ≃ₗ[O]
      (fixedPointOperator n V' P' L' hL').fixedSubmodule := by
  let q := map n V P f hV hP
  let F := fixedPointOperator n V P L hL
  let heq := fixedPointOperator_map n V P f hV hP L L' hL hL' hmap
  let G := kernelEnd q heq
  have hpow (k : ℕ) (x : LinearMap.ker q) :
      ((G ^ k) x : ModifiedModule n V P) = (F ^ k) (x : ModifiedModule n V P) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change F (((G ^ k) x : LinearMap.ker q) : ModifiedModule n V P) = _
      rw [ih]
  have hnil : IsNilpotent G := by
    refine ⟨2 * n + 1, LinearMap.ext fun x => Subtype.ext ?_⟩
    change ((G ^ (2 * n + 1)) x : ModifiedModule n V P) = 0
    rw [hpow]
    exact fixedPointOperator_pow_of_map_eq_zero n V P f hV hP hf hcomm L hL hLcomm hkill hLker
      x (LinearMap.mem_ker.mp x.prop)
  exact fixedSubmoduleLiftEquiv q heq (map_surjective n V P f hV hP hf) hnil

end FixedPointOperator

end Langlands.FormalGroup.Drinfeld.ModifiedModule
