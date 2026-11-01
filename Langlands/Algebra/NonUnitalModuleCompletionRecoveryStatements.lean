import Langlands.Algebra.NonUnitalModuleCompletionFunctor

/-!
# Recovery and faithfulness targets for actual module completion

Renard I.1.5, printed pp.10–11/PDF16–17. These proposition definitions
state recovery of the actual nondegenerate part and faithfulness of the
actual restricted completion functor; they do not prove those assertions.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- Recovery through the exact canonical additive map, with equivariance
and evaluation at every idempotent fixing the actual family. -/
def NonUnitalModuleCompletionPartRecovery (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
  ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
    (nondegeneratePart hA (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
        E.toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
    (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
    (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M)) (e : Idempotent A),
      (e : A) • x.val = x.val → E.symm x = x.val.val e)

/-- Faithfulness of the actual completion functor on original nondegenerate modules. -/
def NondegenerateModuleCompletionFaithful (hA : IsIdempotented A) : Prop :=
  (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Faithful

/-- The recovery and faithfulness clauses of I.1.5, for every original
nondegenerate action at independent scalar and vector universes. -/
def NonUnitalModuleCompletionRecoveryFaithfulnessTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
      IsNondegenerate A M → NonUnitalModuleCompletionPartRecovery hA M) ∧
    NondegenerateModuleCompletionFaithful.{uA, uM} hA

/-! Complete unapplied interfaces at independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleCompletionPartRecovery.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NondegenerateModuleCompletionFaithful.{uA, uM}

example : Prop := NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{uA, uM}

/-! Exact bodies retain the named family action and the entire canonical map. -/

example (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) :
    NonUnitalModuleCompletionPartRecovery hA M =
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
         (nondegeneratePart hA (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
             E.toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
         (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
         (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M)) (e : Idempotent A),
           (e : A) • x.val = x.val → E.symm x = x.val.val e)) := rfl

example (hA : IsIdempotented A) :
    NondegenerateModuleCompletionFaithful.{uA, uM} hA =
      (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Faithful := rfl

example :
    NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{uA, uM} =
      (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
          IsNondegenerate A M →
            (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
             ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
               (nondegeneratePart hA
                   (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
                   E.toAddMonoidHom =
                 NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
               (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
               (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M))
                 (e : Idempotent A),
                 (e : A) • x.val = x.val → E.symm x = x.val.val e))) ∧
        (nondegenerateModuleCompletionFunctor.{uA, uM} hA).Faithful) := rfl

/-! A competing family action does not replace the action specified in the target. -/

example (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A)
    (other : NonUnitalModule A (NonUnitalModuleLeftLimit A M)) :
    let _ := other
    NonUnitalModuleCompletionPartRecovery hA M =
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
         (nondegeneratePart hA (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
             E.toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
         (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
         (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M)) (e : Idempotent A),
           (e : A) • x.val = x.val → E.symm x = x.val.val e)) := rfl

/-! Unequal universe assignments. -/

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type 1) → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleCompletionPartRecovery.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    (M : Type 0) → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @NonUnitalModuleCompletionPartRecovery.{1, 0}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NondegenerateModuleCompletionFaithful.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A → Prop :=
  @NondegenerateModuleCompletionFaithful.{1, 0}

example : Prop := NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{0, 1}
example : Prop := NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{1, 0}

example {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) :
    NondegenerateModuleCompletionFaithful.{0, 1} hA =
      (nondegenerateModuleCompletionFunctor.{0, 1} hA).Faithful := rfl

example {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) :
    NondegenerateModuleCompletionFaithful.{1, 0} hA =
      (nondegenerateModuleCompletionFunctor.{1, 0} hA).Faithful := rfl

example {A : Type 0} [NonUnitalRing A]
    (M : Type 1) [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A) :
    NonUnitalModuleCompletionPartRecovery hA M =
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
         (nondegeneratePart hA (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
             E.toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
         (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
         (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M)) (e : Idempotent A),
           (e : A) • x.val = x.val → E.symm x = x.val.val e)) := rfl

example {A : Type 1} [NonUnitalRing A]
    (M : Type 0) [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A) :
    NonUnitalModuleCompletionPartRecovery hA M =
      (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
       ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
         (nondegeneratePart hA (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
             E.toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
         (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
         (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M)) (e : Idempotent A),
           (e : A) • x.val = x.val → E.symm x = x.val.val e)) := rfl

example :
    NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{0, 1} =
      (∀ (A : Type 0) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (M : Type 1) [AddCommGroup M] [NonUnitalModule A M],
          IsNondegenerate A M →
            (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
             ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
               (nondegeneratePart hA
                   (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
                   E.toAddMonoidHom =
                 NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
               (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
               (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M))
                 (e : Idempotent A),
                 (e : A) • x.val = x.val → E.symm x = x.val.val e))) ∧
        (nondegenerateModuleCompletionFunctor.{0, 1} hA).Faithful) := rfl

example :
    NonUnitalModuleCompletionRecoveryFaithfulnessTheorem.{1, 0} =
      (∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (M : Type 0) [AddCommGroup M] [NonUnitalModule A M],
          IsNondegenerate A M →
            (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := M) hA
             ∃ E : M ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A M),
               (nondegeneratePart hA
                   (NonUnitalModuleLeftLimit A M)).subtype.toAddMonoidHom.comp
                   E.toAddMonoidHom =
                 NonUnitalModuleLeftLimit.canonical (A := A) (M := M) ∧
               (∀ (a : A) (m : M), E (a • m) = a • E m) ∧
               (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A M))
                 (e : Idempotent A),
                 (e : A) • x.val = x.val → E.symm x = x.val.val e))) ∧
        (nondegenerateModuleCompletionFunctor.{1, 0} hA).Faithful) := rfl

/-! The original same-carrier zero action keeps its actual nondegeneracy hypothesis. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (let _ : NonUnitalModule A A := NonUnitalModule.zero
     IsNondegenerate A A → NonUnitalModuleCompletionPartRecovery hA A) =
      (let _ : NonUnitalModule A A := NonUnitalModule.zero
       IsNondegenerate A A →
         (let _ := NonUnitalModuleLeftLimit.nonUnitalModule (M := A) hA
          ∃ E : A ≃+ nondegeneratePart hA (NonUnitalModuleLeftLimit A A),
            (nondegeneratePart hA
                (NonUnitalModuleLeftLimit A A)).subtype.toAddMonoidHom.comp
                E.toAddMonoidHom =
              NonUnitalModuleLeftLimit.canonical (A := A) (M := A) ∧
            (∀ (a : A) (m : A), E (a • m) = a • E m) ∧
            (∀ (x : nondegeneratePart hA (NonUnitalModuleLeftLimit A A))
              (e : Idempotent A),
              (e : A) • x.val = x.val → E.symm x = x.val.val e))) := rfl

end Langlands.Algebra
