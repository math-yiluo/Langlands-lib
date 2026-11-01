import Langlands.Algebra.NonUnitalModuleDualFunctor
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.RenardExactFunctor

/-!
# Exactness statements for the actual nondegenerate duality

Renard I.4.1, printed p.23 / PDF p.29. These closed propositions state
exactness; their mathematical proofs are separate successors.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory
open NonUnitalModuleDual

universe uA uM uN uP

/-- Both actual contravariant dual functors are additive and exact, with the named
abelian structures on the original categories and their inherited Hom groups. -/
def NonUnitalModuleDualCategoricalExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    letI := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
    ∃ hLeft : (leftToRightFunctor.{uA, uM} hA).Additive,
    ∃ hRight : (rightToLeftFunctor.{uA, uM} hA).Additive,
    letI := hLeft
    letI := hRight
    Langlands.Renard.ContravariantSequenceExact (leftToRightFunctor.{uA, uM} hA) ∧
    Langlands.Renard.ContravariantSequenceExact (rightToLeftFunctor.{uA, uM} hA) ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
      S.Exact → (S.op.map (leftToRightFunctor.{uA, uM} hA)).Exact) ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
      S.ShortExact → (S.op.map (leftToRightFunctor.{uA, uM} hA)).ShortExact) ∧
    (∀ S : ShortComplex (RightNondegenerateModuleCat.{uA, uM} A),
      S.Exact → (S.op.map (rightToLeftFunctor.{uA, uM} hA)).Exact) ∧
    (∀ S : ShortComplex (RightNondegenerateModuleCat.{uA, uM} A),
      S.ShortExact → (S.op.map (rightToLeftFunctor.{uA, uM} hA)).ShortExact)

/-- Exactness and endpoint reversals for the actual pullbacks of specified original
intertwiners, with four independent algebra and carrier universes. -/
def NonUnitalModuleDualMapExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
    (P : Type uP) [AddCommGroup P] [NonUnitalModule A P]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (hP : IsNondegenerate A P)
    (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom A N P),
    letI := fullAction hA hM
    letI := fullAction hA hN
    letI := fullAction hA hP
    (Function.Exact f g →
      Function.Exact (pullback hA hN hP g) (pullback hA hM hN f)) ∧
    (Function.Injective f → Function.Surjective (pullback hA hM hN f)) ∧
    (Function.Surjective f → Function.Injective (pullback hA hM hN f)) ∧
    (Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g →
      Function.Injective (pullback hA hN hP g) ∧
      Function.Exact (pullback hA hN hP g) (pullback hA hM hN f) ∧
      Function.Surjective (pullback hA hM hN f))

/-- The injective-to-surjective reversal without an unused third original module. -/
def NonUnitalModuleDualInjectiveSurjectiveStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Injective f → Function.Surjective (pullback hA hM hN f)

/-- The surjective-to-injective reversal without an unused third original module. -/
def NonUnitalModuleDualSurjectiveInjectiveStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Surjective f → Function.Injective (pullback hA hM hN f)

end Langlands.Algebra
