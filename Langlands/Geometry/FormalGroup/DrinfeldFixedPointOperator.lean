import Langlands.Geometry.FormalGroup.DrinfeldModifiedModule

/-! # The fixed-point operator attached to a Frobenius lift -/

noncomputable section

namespace Langlands.FormalGroup.Drinfeld.ModifiedModule

variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
variable (n : ℕ) (V P : Module.End O M)

private def shiftLeft : Module.End O (Fin (n + 1) → M) :=
  LinearMap.pi (Fin.lastCases 0 (fun i => LinearMap.proj i.succ))

private theorem shiftLeft_single_zero (x : M) :
    shiftLeft (O := O) n (Pi.single 0 x) = 0 := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [shiftLeft]
  · simp [shiftLeft, LinearMap.proj_apply]

private theorem shiftLeft_single_succ (j : Fin n) (x : M) :
    shiftLeft (O := O) n (Pi.single j.succ x) = Pi.single j.castSucc x := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [shiftLeft]
  · simp only [shiftLeft, LinearMap.pi_apply, Fin.lastCases_castSucc, LinearMap.proj_apply]
    by_cases h : i = j
    · subst j
      simp
    · rw [Pi.single_eq_of_ne (fun he => h (Fin.succ_injective _ he)),
        Pi.single_eq_of_ne (fun he => h (Fin.castSucc_injective _ he))]

private def liftAndShift (L : M →ₗ[O] ModifiedModule n V P) :
    (Fin (n + 1) → M) →ₗ[O] ModifiedModule n V P :=
  L.comp (LinearMap.proj 0) + (modifiedRelations n V P).mkQ.comp (shiftLeft n)

private theorem liftAndShift_kills_relation (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x)) (i : Fin n) (x : M) :
    liftAndShift n V P L (adjacentRelation n V P i x) = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hs (j : Fin (n + 2)) (y : M) :
        liftAndShift (n + 1) V P L (Pi.single j y) =
          L ((Pi.single j y : Fin (n + 2) → M) 0) +
            (modifiedRelations (n + 1) V P).mkQ (shiftLeft (n + 1) (Pi.single j y)) := rfl
    change liftAndShift (n + 1) V P L
      (Pi.single i.castSucc (V x) - Pi.single i.succ (P x)) = 0
    rw [map_sub, hs, hs, sub_eq_zero]
    refine Fin.cases ?_ (fun j => ?_) i
    · change L ((Pi.single 0 (V x) : Fin (n + 2) → M) 0) +
          (modifiedRelations (n + 1) V P).mkQ (shiftLeft (n + 1) (Pi.single 0 (V x))) =
        L ((Pi.single (Fin.succ (0 : Fin (n + 1))) (P x) : Fin (n + 2) → M) 0) +
          (modifiedRelations (n + 1) V P).mkQ
            (shiftLeft (n + 1) (Pi.single (Fin.succ (0 : Fin (n + 1))) (P x)))
      rw [Pi.single_eq_same, shiftLeft_single_zero, map_zero, add_zero,
        Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm, map_zero, zero_add,
        shiftLeft_single_succ, hL]
      rfl
    · have hj : j.succ.castSucc = j.castSucc.succ := Fin.ext rfl
      rw [hj, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
        Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm, map_zero, zero_add, zero_add,
        shiftLeft_single_succ, shiftLeft_single_succ]
      exact slot_adjacent (n + 1) V P j.castSucc x

/-- A lift satisfying the adjacent-slot relation gives the endomorphism used for fixed points. -/
def fixedPointOperator (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x)) : Module.End O (ModifiedModule n V P) := by
  refine (modifiedRelations n V P).liftQ (liftAndShift n V P L) (iSup_le fun i => ?_)
  rintro _ ⟨x, rfl⟩
  exact LinearMap.mem_ker.mpr (liftAndShift_kills_relation n V P L hL i x)

@[simp]
theorem fixedPointOperator_mkQ (L : M →ₗ[O] ModifiedModule n V P)
    (hL : ∀ x, L (V x) = slot n V P 0 (P x)) (x : Fin (n + 1) → M) :
    fixedPointOperator n V P L hL ((modifiedRelations n V P).mkQ x) =
      L (x 0) + (modifiedRelations n V P).mkQ
        (Fin.lastCases (motive := fun _ => M) 0 (fun i => x i.succ)) := by
  have hshift : shiftLeft (O := O) n x =
      Fin.lastCases (motive := fun _ => M) 0 (fun i => x i.succ) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [shiftLeft, LinearMap.proj_apply]
  change L (x 0) + (modifiedRelations n V P).mkQ (shiftLeft (O := O) n x) = _
  rw [hshift]

/-- A morphism of the underlying operators and the lift also intertwines the fixed-point operators. -/
theorem fixedPointOperator_map {M' : Type*} [AddCommGroup M'] [Module O M']
    {V' P' : Module.End O M'} (f : M →ₗ[O] M')
    (hV : ∀ x, f (V x) = V' (f x)) (hP : ∀ x, f (P x) = P' (f x))
    (L : M →ₗ[O] ModifiedModule n V P) (L' : M' →ₗ[O] ModifiedModule n V' P')
    (hL : ∀ x, L (V x) = slot n V P 0 (P x))
    (hL' : ∀ x, L' (V' x) = slot n V' P' 0 (P' x))
    (hmap : ∀ x, map n V P f hV hP (L x) = L' (f x)) :
    (map n V P f hV hP).comp (fixedPointOperator n V P L hL) =
      (fixedPointOperator n V' P' L' hL').comp (map n V P f hV hP) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (modifiedRelations n V P).mkQ_surjective y
  simp only [LinearMap.comp_apply, fixedPointOperator_mkQ, map_add, map_mkQ, hmap]
  apply congrArg (L' (f (x 0)) + ·)
  apply congrArg (modifiedRelations n V' P').mkQ
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

/-- An injective weighted sum identifies the adjacent-slot relation of a Frobenius lift. -/
theorem liftV_eq_firstSlot (hcomm : Commute P V) (π : O)
    (hp : P ^ (n + 1) = algebraMap O (Module.End O M) π)
    (F : Module.End O M) (hf : F * V = algebraMap O (Module.End O M) π)
    (L : M →ₗ[O] ModifiedModule n V P) (hL : (toDieudonne n V P hcomm).comp L = F)
    (hinj : Function.Injective (toDieudonne n V P hcomm)) (x : M) :
    L (V x) = slot n V P 0 (P x) := by
  apply hinj
  rw [show toDieudonne n V P hcomm (L (V x)) = F (V x) from LinearMap.congr_fun hL (V x),
    toDieudonne_slot]
  change (F * V) x = ((P ^ n * V ^ 0) * P) x
  rw [pow_zero, mul_one, ← pow_succ, hp, hf]

end Langlands.FormalGroup.Drinfeld.ModifiedModule
