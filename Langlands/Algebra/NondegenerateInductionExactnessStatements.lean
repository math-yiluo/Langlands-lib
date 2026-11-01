import Langlands.Algebra.NondegenerateTensorFunctor
import Langlands.Algebra.RenardHomFunctors
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.Renard.HomExactnessComparison

/-!
# Exactness and injective preservation for the actual induction functors

Closed statement targets for Renard I.2.4, printed pp.18–19 / PDF24–25.
The exactness targets allow arbitrary source carrier universe `v`; injectivity
uses the common carrier universe `max uB v`. These declarations are statements.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra

universe uA uB v

/-- Renard I.2.4 for the specified A–B actions, with the right regular B-action. -/
def NondegenerateFInductionExactnessTheorem : Prop :=
  ∀ (A : Type uA) (B : Type uB) [a : NonUnitalRing A] [b : NonUnitalRing B]
    (hA : IsIdempotented A) (hB : IsIdempotented B)
    [left : NonUnitalModule A B]
    (hAB : @ActionsCommute A B B a b _ left (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B a b _ left
      (NonUnitalModule.rightRegular B)),
    (letI := NondegenerateModuleCat.abelian.{uB, v} B hB
     letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
     Langlands.Renard.SequenceExact
       (@NondegenerateTensorFunctor.F.{uA, uB, v} A B a b left
         (NonUnitalModule.rightRegular B) hA hAB hnd)) ∧
    (letI := NondegenerateModuleCat.abelian.{uA, v} A hA
     letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
     Langlands.Renard.SequenceLeftExact
       (@RenardHomFunctors.I.{uA, uB, v} A B a b left hAB hB))

/-- Renard I.2.4 for the independent B–A family, with the left regular B-action. -/
def NondegeneratePInductionExactnessTheorem : Prop :=
  ∀ (A : Type uA) (B : Type uB) [a : NonUnitalRing A] [b : NonUnitalRing B]
    (hA : IsIdempotented A) (hB : IsIdempotented B)
    [right : NonUnitalModule Aᵐᵒᵖ B]
    (hBA : @ActionsCommute B A B b a _ (NonUnitalModule.regular B) right)
    (hnd : @IsNondegenerateBimodule B A B b a _ (NonUnitalModule.regular B) right),
    (letI := NondegenerateModuleCat.abelian.{uB, v} B hB
     letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
     Langlands.Renard.SequenceLeftExact
       (@RenardHomFunctors.pseudoF.{uA, uB, v} A B a b right hBA hA)) ∧
    (letI := NondegenerateModuleCat.abelian.{uA, v} A hA
     letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
     Langlands.Renard.SequenceRightExact
       (@NondegenerateTensorFunctor.P.{uA, uB, v} A B a b
         (NonUnitalModule.regular B) right hB hBA hnd))

/-- Renard's injectivity corollary, in source exact-Hom and Mathlib forms.
Both categories have carrier universe `max uB v`, and I is specialized there. -/
def NondegenerateIInductionInjectivityTheorem : Prop :=
  ∀ (A : Type uA) (B : Type uB) [a : NonUnitalRing A] [b : NonUnitalRing B]
    (hA : IsIdempotented A) (hB : IsIdempotented B)
    [left : NonUnitalModule A B]
    (hAB : @ActionsCommute A B B a b _ left (NonUnitalModule.rightRegular B))
    (_hnd : @IsNondegenerateBimodule A B B a b _ left
      (NonUnitalModule.rightRegular B)),
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    ∀ X : NondegenerateModuleCat.{uA, max uB v} A,
      (Langlands.Renard.HomInjective X →
        Langlands.Renard.HomInjective
          ((@RenardHomFunctors.I.{uA, uB, max uB v} A B a b left hAB hB).obj X)) ∧
      (CategoryTheory.Injective X →
        CategoryTheory.Injective
          ((@RenardHomFunctors.I.{uA, uB, max uB v} A B a b left hAB hB).obj X))

end Langlands.Algebra
