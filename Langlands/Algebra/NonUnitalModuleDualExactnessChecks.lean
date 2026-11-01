import Langlands.Algebra.NonUnitalModuleDualExactnessStatements

/-!
# Interface checks for actual nondegenerate dual exactness statements

These examples inspect proposition definitions and conditional applications.
They do not prove any of the exactness targets.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory
open NonUnitalModuleDual

universe uA uM uN uP

/-! Complete closed interface and exact unfolding of `NonUnitalModuleDualCategoricalExactnessStatement`. -/

example : Prop := @NonUnitalModuleDualCategoricalExactnessStatement.{uA, uM}

example : NonUnitalModuleDualCategoricalExactnessStatement.{uA, uM} =
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
      S.ShortExact → (S.op.map (rightToLeftFunctor.{uA, uM} hA)).ShortExact) := rfl

example : Prop := @NonUnitalModuleDualCategoricalExactnessStatement.{0, 1}

example : NonUnitalModuleDualCategoricalExactnessStatement.{0, 1} =
  ∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{0, 1} A hA
    letI := NondegenerateModuleCat.abelian.{0, 1} Aᵐᵒᵖ hA.op
    ∃ hLeft : (leftToRightFunctor.{0, 1} hA).Additive,
    ∃ hRight : (rightToLeftFunctor.{0, 1} hA).Additive,
    letI := hLeft
    letI := hRight
    Langlands.Renard.ContravariantSequenceExact (leftToRightFunctor.{0, 1} hA) ∧
    Langlands.Renard.ContravariantSequenceExact (rightToLeftFunctor.{0, 1} hA) ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{0, 1} A),
      S.Exact → (S.op.map (leftToRightFunctor.{0, 1} hA)).Exact) ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{0, 1} A),
      S.ShortExact → (S.op.map (leftToRightFunctor.{0, 1} hA)).ShortExact) ∧
    (∀ S : ShortComplex (RightNondegenerateModuleCat.{0, 1} A),
      S.Exact → (S.op.map (rightToLeftFunctor.{0, 1} hA)).Exact) ∧
    (∀ S : ShortComplex (RightNondegenerateModuleCat.{0, 1} A),
      S.ShortExact → (S.op.map (rightToLeftFunctor.{0, 1} hA)).ShortExact) := rfl

example : Prop := @NonUnitalModuleDualCategoricalExactnessStatement.{1, 0}

example : NonUnitalModuleDualCategoricalExactnessStatement.{1, 0} =
  ∀ (A : Type 1) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
    letI := NondegenerateModuleCat.abelian.{1, 0} A hA
    letI := NondegenerateModuleCat.abelian.{1, 0} Aᵐᵒᵖ hA.op
    ∃ hLeft : (leftToRightFunctor.{1, 0} hA).Additive,
    ∃ hRight : (rightToLeftFunctor.{1, 0} hA).Additive,
    letI := hLeft
    letI := hRight
    Langlands.Renard.ContravariantSequenceExact (leftToRightFunctor.{1, 0} hA) ∧
    Langlands.Renard.ContravariantSequenceExact (rightToLeftFunctor.{1, 0} hA) ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{1, 0} A),
      S.Exact → (S.op.map (leftToRightFunctor.{1, 0} hA)).Exact) ∧
    (∀ S : ShortComplex (NondegenerateModuleCat.{1, 0} A),
      S.ShortExact → (S.op.map (leftToRightFunctor.{1, 0} hA)).ShortExact) ∧
    (∀ S : ShortComplex (RightNondegenerateModuleCat.{1, 0} A),
      S.Exact → (S.op.map (rightToLeftFunctor.{1, 0} hA)).Exact) ∧
    (∀ S : ShortComplex (RightNondegenerateModuleCat.{1, 0} A),
      S.ShortExact → (S.op.map (rightToLeftFunctor.{1, 0} hA)).ShortExact) := rfl

/-! Complete closed interface and exact unfolding of `NonUnitalModuleDualMapExactnessStatement`. -/

example : Prop := @NonUnitalModuleDualMapExactnessStatement.{uA, uM, uN, uP}

example : NonUnitalModuleDualMapExactnessStatement.{uA, uM, uN, uP} =
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
      Function.Surjective (pullback hA hM hN f)) := rfl

example : Prop := @NonUnitalModuleDualMapExactnessStatement.{0, 1, 2, 3}

example : NonUnitalModuleDualMapExactnessStatement.{0, 1, 2, 3} =
  ∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type 2) [AddCommGroup N] [NonUnitalModule A N]
    (P : Type 3) [AddCommGroup P] [NonUnitalModule A P]
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
      Function.Surjective (pullback hA hM hN f)) := rfl

example : Prop := @NonUnitalModuleDualMapExactnessStatement.{3, 2, 1, 0}

example : NonUnitalModuleDualMapExactnessStatement.{3, 2, 1, 0} =
  ∀ (A : Type 3) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type 2) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type 1) [AddCommGroup N] [NonUnitalModule A N]
    (P : Type 0) [AddCommGroup P] [NonUnitalModule A P]
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
      Function.Surjective (pullback hA hM hN f)) := rfl

/-! Specialization to the same assertion on the opposite algebra. -/

example (H : NonUnitalModuleDualMapExactnessStatement.{uA, uM, uN, uP}) :
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (P : Type uP) [AddCommGroup P] [NonUnitalModule Aᵐᵒᵖ P]
    (hM : IsNondegenerate Aᵐᵒᵖ M) (hN : IsNondegenerate Aᵐᵒᵖ N)
    (hP : IsNondegenerate Aᵐᵒᵖ P)
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) (g : NonUnitalModuleHom Aᵐᵒᵖ N P),
    letI := fullAction hA.op hM
    letI := fullAction hA.op hN
    letI := fullAction hA.op hP
    (Function.Exact f g →
      Function.Exact (pullback hA.op hN hP g) (pullback hA.op hM hN f)) ∧
    (Function.Injective f → Function.Surjective (pullback hA.op hM hN f)) ∧
    (Function.Surjective f → Function.Injective (pullback hA.op hM hN f)) ∧
    (Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g →
      Function.Injective (pullback hA.op hN hP g) ∧
      Function.Exact (pullback hA.op hN hP g) (pullback hA.op hM hN f) ∧
      Function.Surjective (pullback hA.op hM hN f)) := by
  intro A _ _ _ _ hA M _ _ N _ _ P _ _ hM hN hP f g
  exact H Aᵐᵒᵖ hA.op M N P hM hN hP f g

/-! Complete closed interface and exact unfolding of `NonUnitalModuleDualInjectiveSurjectiveStatement`. -/

example : Prop := @NonUnitalModuleDualInjectiveSurjectiveStatement.{uA, uM, uN}

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{uA, uM, uN} =
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Injective f → Function.Surjective (pullback hA hM hN f) := rfl

example : Prop := @NonUnitalModuleDualInjectiveSurjectiveStatement.{0, 1, 2}

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{0, 1, 2} =
  ∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type 2) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Injective f → Function.Surjective (pullback hA hM hN f) := rfl

example : Prop := @NonUnitalModuleDualInjectiveSurjectiveStatement.{3, 2, 1}

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{3, 2, 1} =
  ∀ (A : Type 3) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type 2) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type 1) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Injective f → Function.Surjective (pullback hA hM hN f) := rfl

/-! Specialization to the same assertion on the opposite algebra. -/

example (H : NonUnitalModuleDualInjectiveSurjectiveStatement.{uA, uM, uN}) :
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (hM : IsNondegenerate Aᵐᵒᵖ M) (hN : IsNondegenerate Aᵐᵒᵖ N)
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N),
    letI := fullAction hA.op hM
    letI := fullAction hA.op hN
    Function.Injective f → Function.Surjective (pullback hA.op hM hN f) := by
  intro A _ _ _ _ hA M _ _ N _ _ hM hN f
  exact H Aᵐᵒᵖ hA.op M N hM hN f

/-! Complete closed interface and exact unfolding of `NonUnitalModuleDualSurjectiveInjectiveStatement`. -/

example : Prop := @NonUnitalModuleDualSurjectiveInjectiveStatement.{uA, uM, uN}

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{uA, uM, uN} =
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Surjective f → Function.Injective (pullback hA hM hN f) := rfl

example : Prop := @NonUnitalModuleDualSurjectiveInjectiveStatement.{0, 1, 2}

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{0, 1, 2} =
  ∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type 2) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Surjective f → Function.Injective (pullback hA hM hN f) := rfl

example : Prop := @NonUnitalModuleDualSurjectiveInjectiveStatement.{3, 2, 1}

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{3, 2, 1} =
  ∀ (A : Type 3) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type 2) [AddCommGroup M] [NonUnitalModule A M]
    (N : Type 1) [AddCommGroup N] [NonUnitalModule A N]
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N),
    letI := fullAction hA hM
    letI := fullAction hA hN
    Function.Surjective f → Function.Injective (pullback hA hM hN f) := rfl

/-! Specialization to the same assertion on the opposite algebra. -/

example (H : NonUnitalModuleDualSurjectiveInjectiveStatement.{uA, uM, uN}) :
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (hM : IsNondegenerate Aᵐᵒᵖ M) (hN : IsNondegenerate Aᵐᵒᵖ N)
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N),
    letI := fullAction hA.op hM
    letI := fullAction hA.op hN
    Function.Surjective f → Function.Injective (pullback hA.op hM hN f) := by
  intro A _ _ _ _ hA M _ _ N _ _ hM hN f
  exact H Aᵐᵒᵖ hA.op M N hM hN f

/-! The named abelian structures preserve the actual original pointwise Hom groups. -/

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (NondegenerateModuleCat.abelian.{uA, uM} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} A) :=
  NondegenerateModuleCat.abelian_toPreadditive A hA

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{uA, uM} Aᵐᵒᵖ) :=
  NondegenerateModuleCat.abelian_toPreadditive Aᵐᵒᵖ hA.op

/-! Both one-sided conditions, including their boundary mono/epi clauses. -/

example {C : Type uM} {D : Type uN} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : Cᵒᵖ ⥤ D) [F.Additive] :
    Langlands.Renard.ContravariantSequenceExact F ↔
      (∀ S : ShortComplex Cᵒᵖ,
        S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)) ∧
      (∀ S : ShortComplex Cᵒᵖ,
        S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g)) :=
  Iff.rfl

/-! The actual right-to-left functor uses the same pullback function. -/

example (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M N : RightNondegenerateModuleCat.{uA, uM} A) (f : M ⟶ N) :
    ((rightToLeftFunctor hA).map f.op).hom =
      fromDoubleOppositeMap (pullback hA.op M.property N.property f.hom) := rfl

example (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)
    (M N : RightNondegenerateModuleCat.{uA, uM} A) (f : M ⟶ N) :
    ⇑(NonUnitalModuleHom.toAddMonoidHom ((rightToLeftFunctor hA).map f.op).hom) =
      ⇑(NonUnitalModuleHom.toAddMonoidHom
        (pullback hA.op M.property N.property f.hom)) := rfl

end Langlands.Algebra
