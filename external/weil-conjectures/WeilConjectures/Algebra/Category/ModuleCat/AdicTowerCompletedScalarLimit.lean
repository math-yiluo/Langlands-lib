/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Completed scalars on an annihilated tower limit

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
/-- The limit of a tower annihilated at level `n` by `I^(n+1)` has the canonical
completed scalar action. No finiteness or surjectivity hypothesis is needed.
The underlying module and its comparison are specified by the limit universal property;
the residue equation determines the completed action coordinatewise. Thus the pair
`N, e` is unique up to the unique completed-linear isomorphism respecting `e`.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, the sentence defining
`M = lim M_n` as a module over the completion.
(blueprint: lem-weil-pbc-adic-tower-completed-scalar-limit).

Proof: Annihilation makes the scalar endomorphism map A -> End_A(T_n) factor
through A/I^(n+1). Composing it with the completion residue gives d_n(r).
For a representative Cauchy sequence of r, representatives at comparable indices
differ by an element of the smaller ideal power. That power kills the smaller term,
so d_n(r) commutes with transitions. The ordinary A-module limit universal property
lifts these coordinate endomorphisms to an endomorphism v(r) of the limit.
Joint injectivity of the projections proves that v preserves zero, one, addition
and multiplication. Restrict the endomorphism-module action along this ring map to
make the existing limit a module over the completion. For scalars from A the residue
equation recovers the original A-action, so the identity on underlying elements is
the restricted A-linear isomorphism e. The coordinate formula proves the assertion.
The same formula and joint injectivity determine the completed action uniquely
relative to e. -/
theorem adicTower_completedScalarLimit (A : Type u) [CommRing A] (I : Ideal A)
    (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hT : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥) :
    ∃ N : ModuleCat.{u} (AdicCompletion I A),
    ∃ e : (restrictScalars (algebraMap A (AdicCompletion I A))).obj N ≅ limit T,
    ∀ (n : ℕ) (r : AdicCompletion I A) (a : A) (x : N),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (e.hom ≫ limit.π T (op n)) (r • x) =
        a • (e.hom ≫ limit.π T (op n)) x  := by
  classical
  have hz (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1)) (x : T.obj (op n)) : a • x = 0 := by
    have hx : a • x ∈ I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) :=
      Submodule.smul_mem_smul ha (Submodule.mem_top)
    simpa [hT n] using hx
  let c (n : ℕ) : A ⧸ I ^ (n + 1) →+* Module.End A (T.obj (op n)) :=
    Ideal.Quotient.lift _ (Module.toModuleEnd A (T.obj (op n))) (fun a ha ↦ by
      ext x
      exact hz n a ha x)
  have hc (n : ℕ) (a : A) (x : T.obj (op n)) :
      c n (Ideal.Quotient.mk (I ^ (n + 1)) a) x = a • x := rfl
  let d (n : ℕ) : AdicCompletion I A →+* Module.End A (T.obj (op n)) :=
    (c n).comp (AdicCompletion.evalₐ I (n + 1)).toRingHom
  have hd (n : ℕ) (r : AdicCompletion I A) (a : A) (x : T.obj (op n))
      (ha : AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a) :
      d n r x = a • x := by
    change c n (AdicCompletion.evalₐ I (n + 1) r) x = _
    rw [ha, hc]
  have hdcompat (r : AdicCompletion I A) {i j : ℕᵒᵖ} (f : i ⟶ j) :
      ofHom (d i.unop r) ≫ T.map f = T.map f ≫ ofHom (d j.unop r) := by
    induction r using AdicCompletion.induction_on I A with
    | h r =>
      ext x
      simp only [hom_comp, LinearMap.comp_apply, hom_ofHom]
      rw [hd _ _ (r.val (i.unop + 1)) _ (AdicCompletion.evalₐ_mk _ _ _),
        hd _ _ (r.val (j.unop + 1)) _ (AdicCompletion.evalₐ_mk _ _ _), map_smul]
      have hle : j.unop + 1 ≤ i.unop + 1 := Nat.add_le_add_right (leOfHom f.unop) 1
      have heq : Ideal.Quotient.mk (I ^ (j.unop + 1)) (r.val (i.unop + 1)) =
          Ideal.Quotient.mk (I ^ (j.unop + 1)) (r.val (j.unop + 1)) := by
        simpa only [SModEq.def, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.Quotient.mk_eq_mk]
          using (r.property hle).symm
      simpa only [hc] using congrArg (fun a ↦ c j.unop a (T.map f x)) heq
  let v (r : AdicCompletion I A) : limit T ⟶ limit T := limit.lift T
    { pt := limit T
      π :=
        { app j := limit.π T j ≫ ofHom (d j.unop r)
          naturality i j f := by
            dsimp
            rw [Category.id_comp, Category.assoc, hdcompat, ← Category.assoc, limit.w] } }
  have hv (r : AdicCompletion I A) (j : ℕᵒᵖ) (x : ↑(limit T)) :
      limit.π T j (v r x) = d j.unop r (limit.π T j x) := by
    have he : v r ≫ limit.π T j = limit.π T j ≫ ofHom (d j.unop r) :=
      limit.lift_π _ j
    exact congrArg (fun f : limit T ⟶ T.obj j ↦ f x) he
  let ρ : AdicCompletion I A →+* Module.End A ↑(limit T) :=
    { toFun r := (v r).hom
      map_one' := by
        ext x
        apply Concrete.limit_ext T
        intro j
        rw [hv, map_one]
        rfl
      map_mul' r s := by
        ext x
        apply Concrete.limit_ext T
        intro j
        change limit.π T j (v (r * s) x) = limit.π T j (v r (v s x))
        rw [hv, hv, hv, map_mul]
        rfl
      map_zero' := by
        ext x
        apply Concrete.limit_ext T
        intro j
        rw [hv, map_zero]
        simp
      map_add' r s := by
        ext x
        apply Concrete.limit_ext T
        intro j
        change limit.π T j (v (r + s) x) = limit.π T j (v r x + v s x)
        rw [hv, (limit.π T j).hom.map_add, hv, hv, map_add]
        rfl }
  have hva (a : A) (x : ↑(limit T)) : v (algebraMap A (AdicCompletion I A) a) x = a • x := by
    apply Concrete.limit_ext T
    intro j
    rw [hv, map_smul]
    apply hd
    exact (AdicCompletion.evalₐ I (j.unop + 1)).commutes a
  let : Module (AdicCompletion I A) ↑(limit T) := Module.compHom _ ρ
  let N : ModuleCat.{u} (AdicCompletion I A) := ModuleCat.of _ ↑(limit T)
  let e : (restrictScalars (algebraMap A (AdicCompletion I A))).obj N ≅ limit T :=
    { hom := ConcreteCategory.ofHom (C := ModuleCat A)
        (X := (restrictScalars (algebraMap A (AdicCompletion I A))).obj N)
        (Y := limit T)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            exact hva a x }
      inv := ConcreteCategory.ofHom (C := ModuleCat A)
        (X := limit T)
        (Y := (restrictScalars (algebraMap A (AdicCompletion I A))).obj N)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            exact (hva a x).symm }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }
  refine ⟨N, e, ?_⟩
  intro n r a x ha
  change limit.π T (op n) (v r x) = a • limit.π T (op n) x
  rw [hv]
  exact hd n r a _ ha

end ModuleCat
