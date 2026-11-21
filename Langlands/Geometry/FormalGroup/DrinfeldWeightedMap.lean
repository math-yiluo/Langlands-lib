import Langlands.Geometry.FormalGroup.DrinfeldModifiedModule
import Mathlib.Algebra.BigOperators.Fin

/-! # Injectivity of the weighted map of the modified module -/

noncomputable section

open scoped BigOperators

namespace Langlands.FormalGroup.Drinfeld.ModifiedModule

variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
variable (V P : Module.End O M)

private def insertZero (n : ℕ) : (Fin (n + 1) → M) →ₗ[O] (Fin (n + 2) → M) :=
  LinearMap.pi (Fin.cases 0 (fun i => LinearMap.proj i))

private theorem insertZero_single (n : ℕ) (i : Fin (n + 1)) (x : M) :
    insertZero (O := O) n (Pi.single i x) = Pi.single i.succ x := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [insertZero]
  · simp only [insertZero, LinearMap.pi_apply, Fin.cases_succ, LinearMap.proj_apply]
    by_cases he : k = i
    · subst k
      simp
    · rw [Pi.single_eq_of_ne he, Pi.single_eq_of_ne (fun e => he (Fin.succ_injective _ e))]

private theorem insertZero_mem (n : ℕ) {x : Fin (n + 1) → M}
    (hx : x ∈ modifiedRelations n V P) :
    insertZero (O := O) n x ∈ modifiedRelations (n + 1) V P := by
  have hle : modifiedRelations n V P ≤ (modifiedRelations (n + 1) V P).comap (insertZero (O := O) n) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_comap]
    simp only [adjacentRelation, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.single_apply,
      map_sub, insertZero_single]
    exact adjacentRelation_mem (n + 1) V P i.succ y
  exact hle hx

private theorem weighted_sum_succ (hcomm : Commute P V) (n : ℕ) (x : Fin (n + 2) → M) :
    (∑ i : Fin (n + 2), (P ^ (n + 1 - i.val) * V ^ i.val) (x i)) =
      (P ^ (n + 1)) (x 0) + V (∑ i : Fin (n + 1), (P ^ (n - i.val) * V ^ i.val) (x i.succ)) := by
  rw [Fin.sum_univ_succ, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (P ^ (n + 1 - (i.val + 1)) * V ^ (i.val + 1)) (x i.succ) =
    (V * (P ^ (n - i.val) * V ^ i.val)) (x i.succ)
  rw [Nat.add_sub_add_right, ← mul_assoc, ((hcomm.pow_left _).symm).eq, mul_assoc, pow_succ']

private theorem mem_range_of_pow_mem (hP : ∀ x, P x ∈ LinearMap.range V → x ∈ LinearMap.range V)
    (m : ℕ) (x : M) (hx : (P ^ m) x ∈ LinearMap.range V) : x ∈ LinearMap.range V := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    apply ih
    apply hP
    simpa only [pow_succ', Module.End.mul_apply] using hx

private theorem mem_relations_of_weighted_sum_eq_zero (hcomm : Commute P V)
    (hV : Function.Injective V) (hP : ∀ x, P x ∈ LinearMap.range V → x ∈ LinearMap.range V)
    (n : ℕ) (x : Fin (n + 1) → M)
    (hx : (∑ i : Fin (n + 1), (P ^ (n - i.val) * V ^ i.val) (x i)) = 0) :
    x ∈ modifiedRelations n V P := by
  induction n with
  | zero =>
    have hx0 : x 0 = 0 := by simpa [Fin.sum_univ_one] using hx
    have hzero : x = 0 := funext fun i => Fin.cases hx0 (fun j => Fin.elim0 j) i
    rw [hzero]
    exact Submodule.zero_mem _
  | succ n ih =>
    have hfirst : (P ^ (n + 1)) (x 0) ∈ LinearMap.range V := by
      rw [weighted_sum_succ V P hcomm] at hx
      rw [eq_neg_of_add_eq_zero_left hx]
      exact Submodule.neg_mem _ (LinearMap.mem_range_self V _)
    obtain ⟨y, hy⟩ := mem_range_of_pow_mem V P hP _ _ hfirst
    let r := adjacentRelation (n + 1) V P 0 y
    let z := x - r
    have hr : r ∈ modifiedRelations (n + 1) V P := adjacentRelation_mem (n + 1) V P 0 y
    have hz0 : z 0 = 0 := by
      simp [z, r, adjacentRelation, LinearMap.sub_apply, Fin.castSucc_zero, hy]
    have hzsum : (∑ i : Fin (n + 2), (P ^ (n + 1 - i.val) * V ^ i.val) (z i)) = 0 := by
      rw [← toDieudonne_mkQ (n + 1) V P hcomm]
      have hr0 : (modifiedRelations (n + 1) V P).mkQ r = 0 := by
        rwa [← LinearMap.mem_ker, Submodule.ker_mkQ]
      change toDieudonne (n + 1) V P hcomm ((modifiedRelations (n + 1) V P).mkQ (x - r)) = 0
      rw [map_sub, hr0, sub_zero, toDieudonne_mkQ]
      exact hx
    rw [weighted_sum_succ V P hcomm, hz0, map_zero, zero_add] at hzsum
    have htail : (fun i : Fin (n + 1) => z i.succ) ∈ modifiedRelations n V P :=
      ih _ (hV (hzsum.trans (map_zero V).symm))
    have htuple : insertZero (O := O) n (fun i => z i.succ) = z := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [insertZero, hz0]
      · simp [insertZero, LinearMap.proj_apply]
    have hz : z ∈ modifiedRelations (n + 1) V P :=
      htuple ▸ insertZero_mem V P n htail
    have he : x = z + r := (sub_add_cancel x r).symm
    exact he ▸ (modifiedRelations (n + 1) V P).add_mem hz hr

/-- A regular uniformizer action modulo Verschiebung makes the weighted map injective. -/
theorem toDieudonne_injective (hcomm : Commute P V) (n : ℕ)
    (hV : Function.Injective V) (hP : ∀ x, P x ∈ LinearMap.range V → x ∈ LinearMap.range V) :
    Function.Injective (toDieudonne n V P hcomm) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨x, rfl⟩ := (modifiedRelations n V P).mkQ_surjective z
  rw [toDieudonne_mkQ] at hz
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact mem_relations_of_weighted_sum_eq_zero V P hcomm hV hP n x hz

/-- A regular scalar power on the tangent quotient suffices for injectivity. -/
theorem toDieudonne_injective_of_scalar (hcomm : Commute P V) (n : ℕ)
    (hV : Function.Injective V) (π : O)
    (hp : P ^ (n + 1) = algebraMap O (Module.End O M) π)
    (hπ : Function.Injective (fun x : M ⧸ LinearMap.range V => π • x)) :
    Function.Injective (toDieudonne n V P hcomm) := by
  apply toDieudonne_injective V P hcomm n hV
  intro x hx
  obtain ⟨y, hy⟩ := hx
  have hscalar : π • x ∈ LinearMap.range V := by
    refine ⟨(P ^ n) y, ?_⟩
    calc
      V ((P ^ n) y) = (P ^ n) (V y) := LinearMap.congr_fun (hcomm.pow_left n).symm.eq y
      _ = (P ^ (n + 1)) x := by rw [hy, pow_succ]; rfl
      _ = π • x := by rw [hp, Module.algebraMap_end_apply]
  rw [← (LinearMap.range V).ker_mkQ, LinearMap.mem_ker] at hscalar ⊢
  apply hπ
  simpa only [map_smul, smul_zero] using hscalar

/-- A map into the weighted image has a canonical lift when the weighted map is injective. -/
def liftWeightedMap (hcomm : Commute P V) (n : ℕ)
    (hV : Function.Injective V) (hP : ∀ x, P x ∈ LinearMap.range V → x ∈ LinearMap.range V)
    (F : Module.End O M) (hF : LinearMap.range F ≤ LinearMap.range (toDieudonne n V P hcomm)) :
    {L : M →ₗ[O] ModifiedModule n V P // (toDieudonne n V P hcomm).comp L = F} := by
  let e := LinearEquiv.ofInjective (toDieudonne n V P hcomm) (toDieudonne_injective V P hcomm n hV hP)
  refine ⟨e.symm.toLinearMap.comp (F.codRestrict _ (fun x => hF (LinearMap.mem_range_self F x))), ?_⟩
  apply LinearMap.ext
  intro x
  let y : LinearMap.range (toDieudonne n V P hcomm) := ⟨F x, hF (LinearMap.mem_range_self F x)⟩
  change toDieudonne n V P hcomm (e.symm y) = (y : M)
  exact congrArg Subtype.val (e.apply_symm_apply y)

end Langlands.FormalGroup.Drinfeld.ModifiedModule
