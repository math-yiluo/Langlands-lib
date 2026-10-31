import Langlands.Algebra.RegularModuleHom

/-!
# Actual regular-Hom to left-limit comparison targets

Renard I.1.4, printed p.10/PDF16: evaluation on actual idempotents is
an additive isomorphism, with reconstruction at every right local unit.
The assertion retains every original target action.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM

/-- The actual evaluation equivalence, its universal reconstruction formula,
and its compatibility with the two original-vector maps. -/
def RegularModuleHomLeftLimitComparison (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  ∃ E : RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M,
    E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
    (∀ (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A),
      a * (e : A) = a → E.symm x a = a • x.val e) ∧
    E.toAddMonoidHom.comp
        (RegularModuleHom.canonical (A := A) (M := M)).toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical

/-- Finite local units suffice for the actual comparison for every original action. -/
def RegularModuleHomLeftLimitComparisonTheorem : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
    IsIdempotented A → RegularModuleHomLeftLimitComparison A M

/-! Complete unapplied interfaces and exact-body checks at independent universes. -/

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  RegularModuleHomLeftLimitComparison.{uA, uM}

example : (A : Type) → (M : Type 1) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  RegularModuleHomLeftLimitComparison.{0, 1}

example : (A : Type 1) → (M : Type) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  RegularModuleHomLeftLimitComparison.{1, 0}

example : Prop := RegularModuleHomLeftLimitComparisonTheorem.{uA, uM}
example : Prop := RegularModuleHomLeftLimitComparisonTheorem.{0, 1}
example : Prop := RegularModuleHomLeftLimitComparisonTheorem.{1, 0}

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    RegularModuleHomLeftLimitComparison A M =
      (∃ E : RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M,
        E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
        (∀ (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A),
          a * (e : A) = a → E.symm x a = a • x.val e) ∧
        E.toAddMonoidHom.comp
            (RegularModuleHom.canonical (A := A) (M := M)).toAddMonoidHom =
          NonUnitalModuleLeftLimit.canonical) := rfl

example : RegularModuleHomLeftLimitComparisonTheorem.{uA, uM} =
    (∀ (A : Type uA) (M : Type uM)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      IsIdempotented A →
        ∃ E : RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M,
          E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
          (∀ (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A),
            a * (e : A) = a → E.symm x a = a • x.val e) ∧
          E.toAddMonoidHom.comp
              (RegularModuleHom.canonical (A := A) (M := M)).toAddMonoidHom =
            NonUnitalModuleLeftLimit.canonical) := rfl

example : RegularModuleHomLeftLimitComparisonTheorem.{0, 1} =
    (∀ (A : Type) (M : Type 1)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      IsIdempotented A →
        ∃ E : RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M,
          E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
          (∀ (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A),
            a * (e : A) = a → E.symm x a = a • x.val e) ∧
          E.toAddMonoidHom.comp
              (RegularModuleHom.canonical (A := A) (M := M)).toAddMonoidHom =
            NonUnitalModuleLeftLimit.canonical) := rfl

example : RegularModuleHomLeftLimitComparisonTheorem.{1, 0} =
    (∀ (A : Type 1) (M : Type)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      IsIdempotented A →
        ∃ E : RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M,
          E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
          (∀ (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A),
            a * (e : A) = a → E.symm x a = a • x.val e) ∧
          E.toAddMonoidHom.comp
              (RegularModuleHom.canonical (A := A) (M := M)).toAddMonoidHom =
            NonUnitalModuleLeftLimit.canonical) := rfl

/-- Equal carriers retain the zero target action and the regular source multiplication. -/
example (A : Type uA) [NonUnitalRing A] :
    @RegularModuleHomLeftLimitComparison A A _ _
        (NonUnitalModule.zero (A := A) (M := A)) =
      (letI : NonUnitalModule A A := NonUnitalModule.zero (A := A) (M := A)
       ∃ E : RegularModuleHom A A ≃+ NonUnitalModuleLeftLimit A A,
         E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
         (∀ (x : NonUnitalModuleLeftLimit A A) (a : A) (e : Idempotent A),
           a * (e : A) = a → E.symm x a = a • x.val e) ∧
         E.toAddMonoidHom.comp
             (RegularModuleHom.canonical (A := A) (M := A)).toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical) := rfl

/-- With the zero target action on equal carriers, the inverse formula reduces to `0`,
not to the source multiplication. -/
example (A : Type uA) [NonUnitalRing A] :
    @RegularModuleHomLeftLimitComparison A A _ _
        (NonUnitalModule.zero (A := A) (M := A)) =
      (letI : NonUnitalModule A A := NonUnitalModule.zero (A := A) (M := A)
       ∃ E : RegularModuleHom A A ≃+ NonUnitalModuleLeftLimit A A,
         E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
         (∀ (x : NonUnitalModuleLeftLimit A A) (a : A) (e : Idempotent A),
           a * (e : A) = a → E.symm x a = 0) ∧
         E.toAddMonoidHom.comp
             (RegularModuleHom.canonical (A := A) (M := A)).toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical) := rfl

/-- With the regular target action on equal carriers, the inverse formula is multiplication. -/
example (A : Type uA) [NonUnitalRing A] :
    @RegularModuleHomLeftLimitComparison A A _ _ (NonUnitalModule.regular A) =
      (letI : NonUnitalModule A A := NonUnitalModule.regular A
       ∃ E : RegularModuleHom A A ≃+ NonUnitalModuleLeftLimit A A,
         E.toAddMonoidHom = RegularModuleHom.toLeftLimit ∧
         (∀ (x : NonUnitalModuleLeftLimit A A) (a : A) (e : Idempotent A),
           a * (e : A) = a → E.symm x a = a * x.val e) ∧
         E.toAddMonoidHom.comp
             (RegularModuleHom.canonical (A := A) (M := A)).toAddMonoidHom =
           NonUnitalModuleLeftLimit.canonical) := rfl

end Langlands.Algebra
