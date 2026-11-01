import Langlands.Algebra.NonUnitalModuleCorner
import Langlands.Algebra.NonUnitalModuleAmbientAbelianProof
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.RenardExactFunctor

/-!
# Exactness statements for the actual corner functor

Renard (9 July 2026), I.3.1, printed p.19 / PDF25, with the sequence
conventions of A.VIII.1. The ambient assertion is an internal arbitrary-ring
generalization; the nondegenerate assertion retains the underlying original
modules of the source. These propositions have no proofs in this unit.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

/-- Exactness of the actual corner functor on all original nonunital modules. -/
def NonUnitalModuleCornerExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A),
    letI := NonUnitalModuleCat.abelian.{uA, uM} A
    letI := Idempotent.Corner.ring e
    Langlands.Renard.SequenceExact (NonUnitalModuleCorner.functor.{uA, uM} e) ∧
      ∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
        S.Exact → (S.map (NonUnitalModuleCorner.functor e)).Exact

/-- Renard I.3.1 for the actual nondegenerate original-module corner functor. -/
def NondegenerateModuleCornerExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    letI := Idempotent.Corner.ring e
    Langlands.Renard.SequenceExact
        (NonUnitalModuleCorner.nondegenerateFunctor.{uA, uM} e) ∧
      ∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
        S.Exact → (S.map (NonUnitalModuleCorner.nondegenerateFunctor e)).Exact

/-! Closed interfaces, including both unequal universe pairs. -/

example : Prop := @NonUnitalModuleCornerExactnessStatement.{uA, uM}
example : Prop := @NondegenerateModuleCornerExactnessStatement.{uA, uM}
example : Prop := @NonUnitalModuleCornerExactnessStatement.{0, 1}
example : Prop := @NonUnitalModuleCornerExactnessStatement.{1, 0}
example : Prop := @NondegenerateModuleCornerExactnessStatement.{0, 1}
example : Prop := @NondegenerateModuleCornerExactnessStatement.{1, 0}

/-! Exact unfoldings expose the full one-sided tests and arbitrary exact triples. -/

example : NonUnitalModuleCornerExactnessStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A),
      letI := NonUnitalModuleCat.abelian.{uA, uM} A
      letI := Idempotent.Corner.ring e
      ((∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
          S.Exact ∧ Mono S.f →
            (S.map (NonUnitalModuleCorner.functor e)).Exact ∧
              Mono ((NonUnitalModuleCorner.functor e).map S.f)) ∧
        (∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
          S.Exact ∧ Epi S.g →
            (S.map (NonUnitalModuleCorner.functor e)).Exact ∧
              Epi ((NonUnitalModuleCorner.functor e).map S.g))) ∧
        ∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
          S.Exact → (S.map (NonUnitalModuleCorner.functor e)).Exact) := rfl

example : NondegenerateModuleCornerExactnessStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
      letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
      letI := Idempotent.Corner.ring e
      ((∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
          S.Exact ∧ Mono S.f →
            (S.map (NonUnitalModuleCorner.nondegenerateFunctor e)).Exact ∧
              Mono ((NonUnitalModuleCorner.nondegenerateFunctor e).map S.f)) ∧
        (∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
          S.Exact ∧ Epi S.g →
            (S.map (NonUnitalModuleCorner.nondegenerateFunctor e)).Exact ∧
              Epi ((NonUnitalModuleCorner.nondegenerateFunctor e).map S.g))) ∧
        ∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
          S.Exact → (S.map (NonUnitalModuleCorner.nondegenerateFunctor e)).Exact) := rfl

/-! The named abelian data retain exactly the inherited Hom addition. -/

example : (A : Type uA) → [NonUnitalRing A] →
    (NonUnitalModuleCat.abelian.{uA, uM} A).toPreadditive =
      NonUnitalModuleCat.preadditive.{uA, uM} A :=
  @NonUnitalModuleCat.abelian_toPreadditive.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (NondegenerateModuleCat.abelian.{uA, uM} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} A) :=
  @NondegenerateModuleCat.abelian_toPreadditive.{uA, uM}

section ActualData

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)

example (M : NonUnitalModuleCat.{uA, uM} A) :
    letI := Idempotent.Corner.ring e
    letI := NonUnitalModuleCorner.fixedPartAddCommGroup e M
    letI := NonUnitalModuleCorner.fixedPartModule e M
    (NonUnitalModuleCorner.functor e).obj M =
      ModuleCat.of (Idempotent.Corner e) (NonUnitalModuleCorner.FixedPart e M) := rfl

example {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((NonUnitalModuleCorner.functor e).map f).hom =
      NonUnitalModuleCorner.restrict e f := rfl

example : NonUnitalModuleCorner.nondegenerateFunctor.{uA, uM} e =
    nondegenerateInclusion A ⋙ NonUnitalModuleCorner.functor e := rfl

example (M : NondegenerateModuleCat.{uA, uM} A) :
    letI := Idempotent.Corner.ring e
    letI := NonUnitalModuleCorner.fixedPartAddCommGroup e M.obj
    letI := NonUnitalModuleCorner.fixedPartModule e M.obj
    (NonUnitalModuleCorner.nondegenerateFunctor e).obj M =
      ModuleCat.of (Idempotent.Corner e) (NonUnitalModuleCorner.FixedPart e M.obj) := rfl

example {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((NonUnitalModuleCorner.nondegenerateFunctor e).map f).hom =
      NonUnitalModuleCorner.restrict e f.hom := rfl

example (M : NonUnitalModuleCat.{uA, uM} A) :
    NonUnitalModuleCorner.fixedPart (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) M = ⊥ :=
  NonUnitalModuleCorner.fixedPart_zero_idempotent

end ActualData

/-! Regular integers, a trivial carrier, and a nonzero carrier with zero action. -/

section RegularIntegers

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.ofModule ℤ ℤ

example (e : Idempotent ℤ) :
    (NonUnitalModuleCorner.functor.{0, 0} e).obj (NonUnitalModuleCat.of ℤ ℤ) =
      ModuleCat.of (Idempotent.Corner e) (NonUnitalModuleCorner.FixedPart e ℤ) := rfl

example : IsNondegenerate ℤ ℤ := by
  intro m
  exact ⟨⟨1, IsIdempotentElem.one⟩, one_smul ℤ m⟩

example (e : Idempotent ℤ) :
    let M : NondegenerateModuleCat.{0, 0} ℤ :=
      ⟨NonUnitalModuleCat.of ℤ ℤ, fun m =>
        ⟨⟨1, IsIdempotentElem.one⟩, one_smul ℤ m⟩⟩
    (NonUnitalModuleCorner.nondegenerateFunctor e).obj M =
      ModuleCat.of (Idempotent.Corner e) (NonUnitalModuleCorner.FixedPart e M.obj) := rfl

end RegularIntegers

section TrivialCarrier

variable (A : Type uA) [NonUnitalRing A]

local instance : NonUnitalModule A PUnit := NonUnitalModule.zero

example : IsNondegenerate A PUnit := by
  intro m
  exact ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

example (e : Idempotent A) :
    (NonUnitalModuleCorner.functor.{uA, 0} e).obj (NonUnitalModuleCat.of A PUnit) =
      ModuleCat.of (Idempotent.Corner e) (NonUnitalModuleCorner.FixedPart e PUnit) := rfl

example (e : Idempotent A) :
    let M : NondegenerateModuleCat.{uA, 0} A :=
      ⟨NonUnitalModuleCat.of A PUnit, fun _ =>
        ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩⟩
    (NonUnitalModuleCorner.nondegenerateFunctor e).obj M =
      ModuleCat.of (Idempotent.Corner e) (NonUnitalModuleCorner.FixedPart e M.obj) := rfl

end TrivialCarrier

section ZeroIntegerAction

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.zero

example : (NonUnitalModuleCat.of ℤ ℤ).isModule =
    (NonUnitalModule.zero : NonUnitalModule ℤ ℤ) := rfl

example (e : Idempotent ℤ) : NonUnitalModuleCorner.fixedPart e ℤ = ⊥ :=
  NonUnitalModuleCorner.fixedPart_zero_action e

example : ¬ IsNondegenerate ℤ ℤ := by
  intro h
  obtain ⟨e, he⟩ := h 1
  exact (zero_ne_one : (0 : ℤ) ≠ 1) he

end ZeroIntegerAction

end Langlands.Algebra
