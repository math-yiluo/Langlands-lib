import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finite auxiliary arguments in Henniart's construction

These elementary proposition definitions isolate finite selection, actual
finite Galois enlargement, and finite counting under a group action.
They do not assert the representation-theoretic hypotheses needed to apply them.
-/

namespace Langlands.Henniart

universe uX uY uT uS uR uI uU uF uK

/-- Pairwise separation on a finite candidate set admits a finite test set. -/
def FiniteSeparationStatement
    (X : Type uX) (T : Type uT) (R : Type uR) : Prop :=
  ∀ (P : Set X), P.Finite →
    ∀ (evaluate : X → T → R),
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → ∃ t, evaluate x t ≠ evaluate y t) →
      ∃ tests : Finset T,
        ∀ x ∈ P, ∀ y ∈ P,
          (∀ t ∈ tests, evaluate x t = evaluate y t) → x = y

/-- A finite set of tests can be lifted using surjectivity only on that set. -/
def FiniteTestLiftingStatement (S : Type uS) (T : Type uT) : Prop :=
  ∀ (tests : Finset T) (project : S → T),
    (∀ t ∈ tests, ∃ s, project s = t) →
    ∃ lifts : Finset S,
      (∀ s ∈ lifts, project s ∈ tests) ∧
      (∀ t ∈ tests, ∃ s ∈ lifts, project s = t)

/-- Finite separating tests remain separating after a finite choice of lifts.
The existence of those lifts is a premise, not a conclusion about lower ranks. -/
def FiniteLiftedSeparationStatement
    (X : Type uX) (S : Type uS) (T : Type uT) (R : Type uR) : Prop :=
  ∀ (P : Set X) (evaluate : X → T → R) (tests : Finset T) (project : S → T),
    (∀ x ∈ P, ∀ y ∈ P,
      (∀ t ∈ tests, evaluate x t = evaluate y t) → x = y) →
    (∀ t ∈ tests, ∃ s, project s = t) →
    ∃ lifts : Finset S,
      (∀ s ∈ lifts, project s ∈ tests) ∧
      (∀ x ∈ P, ∀ y ∈ P,
        (∀ s ∈ lifts, evaluate x (project s) = evaluate y (project s)) → x = y)

/-- Finitely many actual finite Galois intermediate fields have a common
finite Galois overfield inside the same ambient extension. -/
def FiniteGaloisEnlargementStatement
    (F : Type uF) (K : Type uK) [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ fields : Finset (IntermediateField F K),
    (∀ E ∈ fields, FiniteDimensional F E ∧ IsGalois F E) →
    ∃ L : IntermediateField F K,
      FiniteDimensional F L ∧ IsGalois F L ∧ ∀ E ∈ fields, E ≤ L

/-- An injection carrying one finite set into another of the same finite
cardinality is onto the second set. Both finiteness hypotheses are explicit. -/
def FiniteCountingStatement (X : Type uX) (Y : Type uY) : Prop :=
  ∀ (f : X → Y) (A : Set X) (B : Set Y),
    A.Finite → B.Finite → A.ncard = B.ncard →
    Set.InjOn f A → Set.MapsTo f A B → Set.SurjOn f A B

/-- Finite equal-count strata meeting every target orbit suffice for global
surjectivity of an equivariant injection. The acting group and the ambient
sets may be infinite; no equality of their infinite cardinalities is used. -/
def FiniteOrbitCountingStatement
    (U : Type uU) (X : Type uX) (Y : Type uY) (I : Type uI)
    [Group U] [MulAction U X] [MulAction U Y] : Prop :=
  ∀ (f : X → Y),
    Function.Injective f →
    (∀ (u : U) (x : X), f (u • x) = u • f x) →
    ∀ (source : I → Set X) (target : I → Set Y),
      (∀ i, (source i).Finite ∧ (target i).Finite ∧
        (source i).ncard = (target i).ncard) →
      (∀ i, Set.MapsTo f (source i) (target i)) →
      (∀ y : Y, ∃ (u : U) (i : I), u • y ∈ target i) →
      Function.Surjective f

/-- The elementary finite auxiliary family. This is not the local-converse,
local finiteness, numerical correspondence or rank-induction theorem. -/
def FiniteAuxiliaryStatement
    (X : Type uX) (Y : Type uY) (T : Type uT) (S : Type uS) (R : Type uR)
    (I : Type uI) (U : Type uU) (F : Type uF) (K : Type uK)
    [Group U] [MulAction U X] [MulAction U Y]
    [Field F] [Field K] [Algebra F K] : Prop :=
  FiniteSeparationStatement X T R ∧
  FiniteTestLiftingStatement S T ∧
  FiniteLiftedSeparationStatement X S T R ∧
  FiniteGaloisEnlargementStatement F K ∧
  FiniteCountingStatement X Y ∧
  FiniteOrbitCountingStatement U X Y I

end Langlands.Henniart
