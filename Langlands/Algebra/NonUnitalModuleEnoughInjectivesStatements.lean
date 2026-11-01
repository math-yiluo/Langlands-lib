import Langlands.Algebra.NonUnitalModuleDualFunctor
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.CategoryTheory.Renard.HomObjectProperties
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Renard I.5.2: actual duals of projectives and enough injectives

The duals retain the original actions, with explicit double-op transport
for the dual of a right module. Only the dual-projectivity lemma assumes
projectivity beyond the stated complex idempotented algebra setting.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra.NonUnitalModuleEnoughInjectives

universe uA uM

/-- The actual dual of a projective is injective, on both original sides. -/
def DualProjectivityStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    letI := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
    (∀ P : NondegenerateModuleCat.{uA, uM} A,
      Langlands.Renard.HomProjective P →
        Langlands.Renard.HomInjective (NonUnitalModuleDual.dualObject hA P)) ∧
    (∀ P : RightNondegenerateModuleCat.{uA, uM} A,
      Langlands.Renard.HomProjective P →
        Langlands.Renard.HomInjective (NonUnitalModuleDual.rightDualObject hA P))

/-- Both actual categories have genuine categorical injective presentations. -/
def EnoughInjectivesStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (_hA : IsIdempotented A),
    EnoughInjectives (NondegenerateModuleCat.{uA, max uA uM} A) ∧
      EnoughInjectives (RightNondegenerateModuleCat.{uA, max uA uM} A)

/-- An embedding exposes monomorphy, original injectivity and exact-Hom injectivity. -/
def InjectiveEmbeddingStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
    letI := NondegenerateModuleCat.abelian.{uA, max uA uM} Aᵐᵒᵖ hA.op
    (∀ M : NondegenerateModuleCat.{uA, max uA uM} A,
      ∃ (J : NondegenerateModuleCat.{uA, max uA uM} A) (f : M ⟶ J),
        Langlands.Renard.HomInjective J ∧ Mono f ∧
          Function.Injective (NonUnitalModuleHom.toAddMonoidHom f.hom)) ∧
    (∀ M : RightNondegenerateModuleCat.{uA, max uA uM} A,
      ∃ (J : RightNondegenerateModuleCat.{uA, max uA uM} A) (f : M ⟶ J),
        Langlands.Renard.HomInjective J ∧ Mono f ∧
          Function.Injective (NonUnitalModuleHom.toAddMonoidHom f.hom))

/-- The dual-projective lemma, enough injectives and actual injective embeddings. -/
def InjectivityAssertions : Prop :=
  DualProjectivityStatement.{uA, uM} ∧
    EnoughInjectivesStatement.{uA, uM} ∧
    InjectiveEmbeddingStatement.{uA, uM}

/-! Closed definitions and both unequal universe orders retain the full interfaces. -/

example : InjectivityAssertions.{uA, uM} =
    (DualProjectivityStatement.{uA, uM} ∧
      EnoughInjectivesStatement.{uA, uM} ∧
      InjectiveEmbeddingStatement.{uA, uM}) := rfl

example : DualProjectivityStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
      letI := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
      (∀ P : NondegenerateModuleCat.{uA, uM} A,
        Langlands.Renard.HomProjective P →
          Langlands.Renard.HomInjective (NonUnitalModuleDual.dualObject hA P)) ∧
      (∀ P : RightNondegenerateModuleCat.{uA, uM} A,
        Langlands.Renard.HomProjective P →
          Langlands.Renard.HomInjective (NonUnitalModuleDual.rightDualObject hA P))) := rfl

example : EnoughInjectivesStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (_hA : IsIdempotented A),
      EnoughInjectives (NondegenerateModuleCat.{uA, max uA uM} A) ∧
        EnoughInjectives (RightNondegenerateModuleCat.{uA, max uA uM} A)) := rfl

example : InjectiveEmbeddingStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
      letI := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
      letI := NondegenerateModuleCat.abelian.{uA, max uA uM} Aᵐᵒᵖ hA.op
      (∀ M : NondegenerateModuleCat.{uA, max uA uM} A,
        ∃ (J : NondegenerateModuleCat.{uA, max uA uM} A) (f : M ⟶ J),
          Langlands.Renard.HomInjective J ∧ Mono f ∧
            Function.Injective (NonUnitalModuleHom.toAddMonoidHom f.hom)) ∧
      (∀ M : RightNondegenerateModuleCat.{uA, max uA uM} A,
        ∃ (J : RightNondegenerateModuleCat.{uA, max uA uM} A) (f : M ⟶ J),
          Langlands.Renard.HomInjective J ∧ Mono f ∧
            Function.Injective (NonUnitalModuleHom.toAddMonoidHom f.hom))) := rfl

example : Prop := InjectivityAssertions.{0, 1}
example : Prop := InjectivityAssertions.{1, 0}

end Langlands.Algebra.NonUnitalModuleEnoughInjectives
