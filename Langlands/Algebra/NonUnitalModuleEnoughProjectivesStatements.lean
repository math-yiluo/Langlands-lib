import Langlands.Algebra.NonUnitalModuleIdempotentIdeal
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.Renard.HomObjectProperties
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Renard I.5.2: ideal projectivity, sums and enough projectives

Statements over the actual nondegenerate category and the original ideal Ae.
The carrier universe contains both the ring and the chosen module universe.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleEnoughProjectives

universe uA uM uI

/-- The actual left ideal Ae is projective in the source exact-Hom sense. -/
def IdealProjectivityStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
    ∀ e : Idempotent A,
      Langlands.Renard.HomProjective
        (NonUnitalModuleIdempotentIdeal.object.{uA, uM} hA e)

/-- Any existing actual direct sum of projectives is projective. -/
def DirectSumProjectivityStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
    ∀ (I : Type uI) (P : I → NondegenerateModuleCat.{uA, max uA uM} A)
      (c : Cofan P),
      IsColimit c →
      (∀ i : I, Langlands.Renard.HomProjective (P i)) →
      Langlands.Renard.HomProjective c.pt

/-- Every actual nondegenerate module is an epimorphic image of a projective. -/
def EnoughProjectivesStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (_hA : IsIdempotented A),
    EnoughProjectives (NondegenerateModuleCat.{uA, max uA uM} A)

/-- The same assertion exposes both the original map and its surjectivity. -/
def SurjectiveProjectiveCoverStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
    ∀ M : NondegenerateModuleCat.{uA, max uA uM} A,
      ∃ (P : NondegenerateModuleCat.{uA, max uA uM} A) (f : P ⟶ M),
        Langlands.Renard.HomProjective P ∧ Epi f ∧
          Function.Surjective (NonUnitalModuleHom.toAddMonoidHom f.hom)

/-- The enough-projectives theorem and its two substantive source proof steps. -/
def ProjectivityAssertions : Prop :=
  IdealProjectivityStatement.{uA, uM} ∧
    DirectSumProjectivityStatement.{uA, uM, uI} ∧
    EnoughProjectivesStatement.{uA, uM} ∧
    SurjectiveProjectiveCoverStatement.{uA, uM}

end Langlands.Algebra.NonUnitalModuleEnoughProjectives
