/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Completed free presentations for adic towers

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/- Surjectivity at level zero propagates upwards: the successor kernel is
annihilated by its own ideal power, so two substitutions in the range suffice. -/
private theorem coordinate_surjective (A : Type u) [CommRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hzero : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥)
    (htrans : ∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1)))))
    (P : Type u) [AddCommGroup P] [Module A P] (p : P →ₗ[A] ↑(limit T))
    (hp : Function.Surjective ((limit.π T (op 0)).hom.comp p)) :
    ∀ n : ℕ, Function.Surjective ((limit.π T (op n)).hom.comp p) := by
  intro n
  induction n with
  | zero => exact hp
  | succ n ih =>
    let f := (limit.π T (op (n + 1))).hom.comp p
    let t := (T.map (homOfLE (Nat.le_succ n)).op).hom
    have ht (a : P) : t (f a) = (limit.π T (op n)) (p a) := by
      exact congrArg (fun k : limit T ⟶ T.obj (op n) ↦ k (p a))
        (limit.w T (homOfLE (Nat.le_succ n)).op)
    have hr : f.range ⊔ I ^ (n + 1) • ⊤ = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨a, ha⟩ := ih (t x)
      change (limit.π T (op n)) (p a) = t x at ha
      have hk : x - f a ∈ LinearMap.ker t := by
        rw [LinearMap.mem_ker, map_sub, ht, ha, sub_self]
      rw [(htrans n).2] at hk
      exact Submodule.mem_sup.mpr ⟨f a, ⟨a, rfl⟩, x - f a, hk, by abel⟩
    have hz : I ^ (n + 1) • (I ^ (n + 1) •
        (⊤ : Submodule A (T.obj (op (n + 1))))) = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← Submodule.mul_smul, ← pow_add]
      calc
        I ^ (n + 1 + (n + 1)) • (⊤ : Submodule A (T.obj (op (n + 1)))) ≤
            I ^ (n + 1 + 1) • ⊤ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        _ = ⊥ := hzero (n + 1)
    have hj : I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1)))) ≤ f.range := by
      nth_rw 1 [← hr]
      rw [Submodule.smul_sup, hz, sup_bot_eq]
      exact Submodule.smul_le_right
    apply LinearMap.range_eq_top.mp
    rwa [sup_of_le_left hj] at hr

/- Correct each successive preimage by an ideal-power multiple. The shifted
sequence, with zero in degree zero, is an adic Cauchy sequence. -/
private theorem compatible_preimages (A : Type u) [CommRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hker : ∀ n : ℕ,
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1)))))
    (P : Type u) [AddCommGroup P] [Module A P] (p : P →ₗ[A] ↑(limit T))
    (hp : ∀ n : ℕ, Function.Surjective ((limit.π T (op n)).hom.comp p))
    (x : ↑(limit T)) :
    ∃ y : AdicCompletion I P, ∀ n : ℕ, ∃ a : P,
      AdicCompletion.eval I P (n + 1) y =
        Submodule.Quotient.mk (p := I ^ (n + 1) • ⊤) a ∧
      (limit.π T (op n)) (p a) = (limit.π T (op n)) x := by
  classical
  let f (n : ℕ) := (limit.π T (op n)).hom.comp p
  have hw (n : ℕ) (z : ↑(limit T)) :
      T.map (homOfLE (Nat.le_succ n)).op ((limit.π T (op (n + 1))) z) =
        (limit.π T (op n)) z :=
    congrArg (fun k : limit T ⟶ T.obj (op n) ↦ k z)
      (limit.w T (homOfLE (Nat.le_succ n)).op)
  have step (n : ℕ) (a : P) (ha : f n a = (limit.π T (op n)) x) :
      ∃ b : P, f (n + 1) b = (limit.π T (op (n + 1))) x ∧
        b - a ∈ (I ^ (n + 1) • ⊤ : Submodule A P) := by
    let z := (limit.π T (op (n + 1))) x - f (n + 1) a
    have hz : z ∈ (I ^ (n + 1) • ⊤ : Submodule A (T.obj (op (n + 1)))) := by
      rw [← hker n, LinearMap.mem_ker]
      change T.map (homOfLE (Nat.le_succ n)).op
        ((limit.π T (op (n + 1))) x - (limit.π T (op (n + 1))) (p a)) = 0
      rw [map_sub, hw, hw]
      exact sub_eq_zero.mpr ha.symm
    have hm : Submodule.map (f (n + 1)) (I ^ (n + 1) • ⊤) =
        I ^ (n + 1) • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hp (n + 1))]
    rw [← hm] at hz
    obtain ⟨c, hc, he⟩ := Submodule.mem_map.mp hz
    refine ⟨a + c, ?_, ?_⟩
    · rw [map_add, he]
      dsimp [z]
      abel
    · simpa using hc
  let a : (n : ℕ) → {a : P // f n a = (limit.π T (op n)) x} := fun n ↦ by
    induction n with
    | zero => exact ⟨Classical.choose (hp 0 ((limit.π T (op 0)) x)),
        Classical.choose_spec (hp 0 ((limit.π T (op 0)) x))⟩
    | succ n an => exact ⟨Classical.choose (step n an.val an.property),
        (Classical.choose_spec (step n an.val an.property)).1⟩
  have ha (n : ℕ) : (a (n + 1)).val - (a n).val ∈
      (I ^ (n + 1) • ⊤ : Submodule A P) :=
    (Classical.choose_spec (step n (a n).val (a n).property)).2
  let s : ℕ → P := fun n ↦ match n with
    | 0 => 0
    | n + 1 => (a n).val
  have hs : ∀ n, s n ≡ s (n + 1) [SMOD (I ^ n • ⊤ : Submodule A P)] := by
    intro n
    cases n with
    | zero => simp [SModEq.top]
    | succ n =>
      apply SModEq.symm
      apply SModEq.sub_mem.mpr
      exact ha n
  let c := AdicCompletion.AdicCauchySequence.mk I P s hs
  refine ⟨AdicCompletion.mk I P c, fun n ↦ ⟨(a n).val, ?_, (a n).property⟩⟩
  rfl

/-- An adic tower admits a surjective completed finite free presentation.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof through the
short exact sequence with middle term the completed finite free module.
(blueprint: lem-weil-pbc-adic-tower-completed-free-surjection).

Proof: Choose generators of T_0 and lift them to the limit by recursive lifting
along the surjective transitions. Compose these lifts with e inverse. Their
images define compatible presentations at all levels from the quotients of
A^d by I^(n+1). Nilpotent Nakayama makes every presentation surjective: the
reduction is the chosen presentation of T_0. Indeed, inductively the composite
T_n → T_0 is surjective with kernel I T_n: lift an I-multiple through the
next surjective transition and use its kernel I^(n+1)T_(n+1) ⊆ I T_(n+1).
Thus T_n/I T_n identifies with T_0, while I^(n+1) kills T_n.
To lift a presentation kernel
vector one level, lift its coordinates arbitrarily. Its image is in
I^(n+1)T_(n+1) by the transition kernel assumption. Correct that image using
I^(n+1) times a vector in the surjective free presentation. This proves
surjectivity of the kernel transitions. Exactness of inverse limits for
surjective kernel transitions gives a surjection from the completion of A^d
to the limit. The completed scalar residue equation and equality detected by
all limit coordinates prove that its composite with e inverse is linear over
the completed ring. This yields the stated q. -/
theorem adicTower_completedFreeSurjection (A : Type u) [CommRing A]
    (I : Ideal A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfinite : Module.Finite A (T.obj (op 0)))
    (hzero : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥)
    (htrans : ∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1)))))
    (N : ModuleCat.{u} (AdicCompletion I A))
    (e : (restrictScalars (algebraMap A (AdicCompletion I A))).obj N ≅ limit T)
    (hscalar : ∀ (n : ℕ) (r : AdicCompletion I A) (a : A) (x : N),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (e.hom ≫ limit.π T (op n)) (r • x) =
        a • (e.hom ≫ limit.π T (op n)) x) :
    ∃ (d : ℕ) (q : AdicCompletion I (Fin d → A) →ₗ[AdicCompletion I A] N),
      Function.Surjective q := by
  classical
  let := hfinite
  obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' A (T.obj (op 0))
  have hπ : Function.Surjective (limit.π T (op 0)) :=
    Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit T)
      (fun n ↦ (htrans n).1)
  choose w hw using fun i : Fin d ↦ hπ (f (Pi.single i 1))
  let p : (Fin d → A) →ₗ[A] ↑(limit T) := Fintype.linearCombination A w
  have hp0 : (limit.π T (op 0)).hom.comp p = f := by
    ext i
    change (limit.π T (op 0))
      (Fintype.linearCombination A w (Pi.single i 1)) = f (Pi.single i 1)
    simpa using hw i
  have hp := coordinate_surjective A I T hzero htrans (Fin d → A) p (hp0 ▸ hf)
  let v : Fin d → N := fun i ↦ e.inv (w i)
  let q : AdicCompletion I (Fin d → A) →ₗ[AdicCompletion I A] N :=
    (Fintype.linearCombination (AdicCompletion I A) v).comp
      (AdicCompletion.piEquivFin I d).toLinearMap
  refine ⟨d, q, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := compatible_preimages A I T (fun n ↦ (htrans n).2)
    (Fin d → A) p hp (e.hom x)
  refine ⟨y, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  apply Concrete.limit_ext T
  intro j
  obtain ⟨n⟩ := j
  obtain ⟨a, ha, hx⟩ := hy n
  have hc (i : Fin d) :
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.piEquivFin I d y i) =
        Ideal.Quotient.mk (I ^ (n + 1)) (a i) := by
    rw [AdicCompletion.piEquivFin_apply]
    change AdicCompletion.evalₐ I (n + 1)
      (AdicCompletion.map I (LinearMap.proj i) y) = _
    have hm : AdicCompletion.eval I A (n + 1)
        (AdicCompletion.map I (LinearMap.proj i) y) =
          Submodule.Quotient.mk (p := I ^ (n + 1) • ⊤) (a i) := by
      change (LinearMap.proj i).reduceModIdeal (I ^ (n + 1))
        (AdicCompletion.eval I (Fin d → A) (n + 1) y) = _
      rw [ha]
      rfl
    rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _)), hm]
    rfl
  calc
    (limit.π T (op n)) (e.hom (q y)) =
        (limit.π T (op n)) (p a) := by
      change (e.hom ≫ limit.π T (op n)) (q y) = _
      simp only [q, p, LinearMap.comp_apply, Fintype.linearCombination_apply,
        map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      erw [hscalar n _ (a i) (v i) (hc i)]
      simp [v]
    _ = (limit.π T (op n)) (e.hom x) := hx

end ModuleCat

