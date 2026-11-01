import Langlands.Algebra.NondegenerateInductionExactnessStatements

/-!
# Interfaces for the actual I.2.4 induction statements

Internal declaration, structure, universe and boundary checks.
None assumes or proves a principal exactness or preservation target.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateInductionExactnessChecks

open NonUnitalModuleTensor (Tensor tmul)

universe uA uB v

/-! Complete unapplied closed types, including both unequal ring assignments
and a ring universe strictly above the source and actual target carrier levels. -/

example : Prop := @NondegenerateFInductionExactnessTheorem.{uA, uB, v}
example : Prop := @NondegeneratePInductionExactnessTheorem.{uA, uB, v}
example : Prop := @NondegenerateIInductionInjectivityTheorem.{uA, uB, v}

example : Prop := @NondegenerateFInductionExactnessTheorem.{0, 1, 0}
example : Prop := @NondegeneratePInductionExactnessTheorem.{0, 1, 0}
example : Prop := @NondegenerateIInductionInjectivityTheorem.{0, 1, 0}

example : Prop := @NondegenerateFInductionExactnessTheorem.{1, 0, 1}
example : Prop := @NondegeneratePInductionExactnessTheorem.{1, 0, 1}
example : Prop := @NondegenerateIInductionInjectivityTheorem.{1, 0, 1}

example : Prop := @NondegenerateFInductionExactnessTheorem.{2, 0, 0}
example : Prop := @NondegeneratePInductionExactnessTheorem.{2, 0, 0}
example : Prop := @NondegenerateIInductionInjectivityTheorem.{2, 0, 0}

/-! Exact unfolding checks retain every internally bound input and named datum. -/

example : NondegenerateFInductionExactnessTheorem.{uA, uB, v} =
  (∀ (A : Type uA) (B : Type uB) [a : NonUnitalRing A] [b : NonUnitalRing B]
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
       (@RenardHomFunctors.I.{uA, uB, v} A B a b left hAB hB))) := rfl

example : NondegeneratePInductionExactnessTheorem.{uA, uB, v} =
  (∀ (A : Type uA) (B : Type uB) [a : NonUnitalRing A] [b : NonUnitalRing B]
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
         (NonUnitalModule.regular B) right hB hBA hnd))) := rfl

example : NondegenerateIInductionInjectivityTheorem.{uA, uB, v} =
  (∀ (A : Type uA) (B : Type uB) [a : NonUnitalRing A] [b : NonUnitalRing B]
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
          ((@RenardHomFunctors.I.{uA, uB, max uB v} A B a b left hAB hB).obj X))) := rfl

/-! The abelian data retain the actual inherited pointwise original Hom groups. -/

example : (A : Type uA) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (NondegenerateModuleCat.abelian.{uA, v} A hA).toPreadditive =
      Preadditive.fullSubcategory (nondegenerateProperty.{uA, v} A) :=
  @NondegenerateModuleCat.abelian_toPreadditive.{uA, v}

example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    (NondegenerateModuleCat.abelian.{uA, max uB v} A hA).toPreadditive =
      (inferInstance : Preadditive (NondegenerateModuleCat.{uA, max uB v} A)) :=
  NondegenerateModuleCat.abelian_toPreadditive A hA

/-! Actual A–B objects, groups, actions and whole maps, at arbitrary source v. -/

section AB

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B]

local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)


example : NondegenerateModuleCat.{uB, v} B ⥤
    NondegenerateModuleCat.{uA, max uB v} A := (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd)

example : NondegenerateModuleCat.{uA, v} A ⥤
    NondegenerateModuleCat.{uB, max uB v} B := (RenardHomFunctors.I.{uA, uB, v} hAB hB)

example : (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).Additive := inferInstance
example : (RenardHomFunctors.I.{uA, uB, v} hAB hB).Additive := inferInstance

example (N : NondegenerateModuleCat.{uB, v} B) :
    ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).obj N).obj.carrier = Tensor B B N.obj := rfl

example (N : NondegenerateModuleCat.{uB, v} B) :
    ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).obj N).obj.isAddCommGroup = NonUnitalModuleTensor.addCommGroup B B N.obj := rfl

example (N : NondegenerateModuleCat.{uB, v} B) :
    ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).obj N).obj.isModule = NonUnitalBimoduleTensor.leftModule hAB N.obj := rfl

example {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hAB hAB (NonUnitalBimoduleHom.id A B B) f.hom := rfl

example {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) (b : B) (m : M.obj) :
    ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).map f).hom.toAddMonoidHom (tmul B B M.obj b m) = tmul B B N.obj b (f.hom.toAddMonoidHom m) := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((RenardHomFunctors.I.{uA, uB, v} hAB hB).obj M).obj.carrier = RenardHomFunctors.inductionPart hAB hB M.obj := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((RenardHomFunctors.I.{uA, uB, v} hAB hB).obj M).obj.isAddCommGroup =
      (inferInstance : AddCommGroup (RenardHomFunctors.inductionPart hAB hB M.obj)) := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((RenardHomFunctors.I.{uA, uB, v} hAB hB).obj M).obj.isModule =
      (inferInstance : NonUnitalModule B (RenardHomFunctors.inductionPart hAB hB M.obj)) := rfl

example (M : NondegenerateModuleCat.{uA, v} A)
    (b b' : B) (φ : ((RenardHomFunctors.I.{uA, uB, v} hAB hB).obj M).obj) :
    (show NonUnitalModuleHom A B M.obj from (b • φ).val) b' =
      (show NonUnitalModuleHom A B M.obj from φ.val) (b' * b) := rfl

example {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((RenardHomFunctors.I.{uA, uB, v} hAB hB).map f).hom =
      (NondegenerateHomFunctor.ambientMap hAB f.hom).restrictNondegeneratePart hB := rfl

example {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N)
    (φ : ((RenardHomFunctors.I.{uA, uB, v} hAB hB).obj M).obj) :
    ((show NonUnitalModuleHom B (RenardHomFunctors.inductionPart hAB hB M.obj)
        (RenardHomFunctors.inductionPart hAB hB N.obj) from ((RenardHomFunctors.I.{uA, uB, v} hAB hB).map f).hom) φ).val =
      f.hom.comp φ.val := rfl

/-! Full one-sided sequence conditions with exactly the named abelian structures. -/

section Sequences


example :
    letI := NondegenerateModuleCat.abelian.{uB, v} B hB
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Langlands.Renard.SequenceExact (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd) ↔
    Langlands.Renard.SequenceLeftExact (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd) ∧ Langlands.Renard.SequenceRightExact (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd) := Iff.rfl

example :
    letI := NondegenerateModuleCat.abelian.{uB, v} B hB
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Langlands.Renard.SequenceLeftExact (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd) ↔
    ∀ S : ShortComplex (NondegenerateModuleCat.{uB, v} B),
      S.Exact ∧ Mono S.f → (S.map (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd)).Exact ∧ Mono ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).map S.f) := Iff.rfl

example :
    letI := NondegenerateModuleCat.abelian.{uB, v} B hB
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Langlands.Renard.SequenceRightExact (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd) ↔
    ∀ S : ShortComplex (NondegenerateModuleCat.{uB, v} B),
      S.Exact ∧ Epi S.g → (S.map (NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd)).Exact ∧ Epi ((NondegenerateTensorFunctor.F.{uA, uB, v} hA hAB hnd).map S.g) := Iff.rfl

end Sequences

section HomSequences


example :
    letI := NondegenerateModuleCat.abelian.{uA, v} A hA
    letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    Langlands.Renard.SequenceLeftExact (RenardHomFunctors.I.{uA, uB, v} hAB hB) ↔
    ∀ S : ShortComplex (NondegenerateModuleCat.{uA, v} A),
      S.Exact ∧ Mono S.f → (S.map (RenardHomFunctors.I.{uA, uB, v} hAB hB)).Exact ∧ Mono ((RenardHomFunctors.I.{uA, uB, v} hAB hB).map S.f) := Iff.rfl

end HomSequences

/-! No transfer from a smaller category: I and both Hom predicates use common w. -/

section CommonCarrier


example : NondegenerateModuleCat.{uB, max uB (max uB v)} B =
    NondegenerateModuleCat.{uB, max uB v} B := rfl

example : NondegenerateModuleCat.{uA, max uB v} A ⥤
    NondegenerateModuleCat.{uB, max uB v} B :=
  RenardHomFunctors.I.{uA, uB, max uB v} hAB hB

example (X : NondegenerateModuleCat.{uA, max uB v} A) :
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    Langlands.Renard.HomInjective X ↔ CategoryTheory.Injective X := by
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  exact Langlands.Renard.homInjectiveComparison X

example (X : NondegenerateModuleCat.{uA, max uB v} A) :
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    let Y := (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj X
    (Langlands.Renard.HomInjective X → Langlands.Renard.HomInjective Y) ↔
      (CategoryTheory.Injective X → CategoryTheory.Injective Y) := by
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  let := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
  dsimp only
  rw [show Langlands.Renard.HomInjective X ↔ CategoryTheory.Injective X from
    Langlands.Renard.homInjectiveComparison X,
    show Langlands.Renard.HomInjective
        ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj X) ↔
      CategoryTheory.Injective
        ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj X) from
      Langlands.Renard.homInjectiveComparison _]

end CommonCarrier
end AB

/-! Independent B–A family: no left A-action is present. -/

section BA

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule Aᵐᵒᵖ B]

local instance : NonUnitalModule B B := NonUnitalModule.regular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)


example : NondegenerateModuleCat.{uA, v} A ⥤
    NondegenerateModuleCat.{uB, max uB v} B := (NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd)

example : NondegenerateModuleCat.{uB, v} B ⥤
    NondegenerateModuleCat.{uA, max uB v} A := (RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA)

example : (NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).Additive := inferInstance
example : (RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).Additive := inferInstance

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).obj M).obj.carrier = Tensor A B M.obj := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).obj M).obj.isAddCommGroup = NonUnitalModuleTensor.addCommGroup A B M.obj := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hBA M.obj := rfl

example {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hBA hBA (NonUnitalBimoduleHom.id B A B) f.hom := rfl

example {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) (b : B) (m : M.obj) :
    ((NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).map f).hom.toAddMonoidHom (tmul A B M.obj b m) = tmul A B N.obj b (f.hom.toAddMonoidHom m) := rfl

example (N : NondegenerateModuleCat.{uB, v} B) :
    ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).obj N).obj.carrier = RenardHomFunctors.pseudoPart hBA hA N.obj := rfl

example (N : NondegenerateModuleCat.{uB, v} B) :
    ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).obj N).obj.isAddCommGroup =
      (inferInstance : AddCommGroup (RenardHomFunctors.pseudoPart hBA hA N.obj)) := rfl

example (N : NondegenerateModuleCat.{uB, v} B) :
    ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).obj N).obj.isModule =
      (inferInstance : NonUnitalModule A (RenardHomFunctors.pseudoPart hBA hA N.obj)) := rfl

example (N : NondegenerateModuleCat.{uB, v} B)
    (a : A) (b : B) (φ : ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).obj N).obj) :
    (show NonUnitalModuleHom B B N.obj from (a • φ).val) b =
      (show NonUnitalModuleHom B B N.obj from φ.val) (op a • b) := rfl

example {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).map f).hom =
      (NondegenerateHomFunctor.ambientMap hBA f.hom).restrictNondegeneratePart hA := rfl

example {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N)
    (φ : ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).obj M).obj) :
    ((show NonUnitalModuleHom A (RenardHomFunctors.pseudoPart hBA hA M.obj)
        (RenardHomFunctors.pseudoPart hBA hA N.obj) from ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).map f).hom) φ).val =
      f.hom.comp φ.val := rfl

section TensorSequences


example :
    letI := NondegenerateModuleCat.abelian.{uA, v} A hA
    letI := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
    Langlands.Renard.SequenceRightExact (NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd) ↔
    ∀ S : ShortComplex (NondegenerateModuleCat.{uA, v} A),
      S.Exact ∧ Epi S.g → (S.map (NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd)).Exact ∧ Epi ((NondegenerateTensorFunctor.P.{uA, uB, v} hB hBA hnd).map S.g) := Iff.rfl

end TensorSequences

section HomSequences


example :
    letI := NondegenerateModuleCat.abelian.{uB, v} B hB
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Langlands.Renard.SequenceLeftExact (RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA) ↔
    ∀ S : ShortComplex (NondegenerateModuleCat.{uB, v} B),
      S.Exact ∧ Mono S.f → (S.map (RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA)).Exact ∧ Mono ((RenardHomFunctors.pseudoF.{uA, uB, v} hBA hA).map S.f) := Iff.rfl

end HomSequences
end BA

/-! Specified source structures are retained while alternatives coexist. -/

section CompetingStructures

set_option linter.unusedSectionVars false

variable (A : Type uA) (B : Type uB)
  (a₀ : NonUnitalRing A) [a₁ : NonUnitalRing A]
  (b₀ : NonUnitalRing B) [b₁ : NonUnitalRing B]
  (hA : @IsIdempotented A a₀) (hB : @IsIdempotented B b₀)

include a₁ b₁

example : (inferInstance : NonUnitalRing A) = a₁ := rfl
example : (inferInstance : NonUnitalRing B) = b₁ := rfl

section AB

variable (left₀ : @NonUnitalModule A B a₀ b₀.toAddCommGroup)
  [left₁ : @NonUnitalModule A B a₁ b₁.toAddCommGroup]
  [otherRight : NonUnitalModule Bᵐᵒᵖ B]
  (hAB : @ActionsCommute A B B a₀ b₀ b₀.toAddCommGroup left₀
    (@NonUnitalModule.rightRegular B b₀))
  (hnd : @IsNondegenerateBimodule A B B a₀ b₀ b₀.toAddCommGroup left₀
    (@NonUnitalModule.rightRegular B b₀))

include left₁ otherRight

example : (inferInstance : NonUnitalModule A B) = left₁ := rfl
example : (inferInstance : NonUnitalModule Bᵐᵒᵖ B) = otherRight := rfl

example :
    letI := a₀
    letI := b₀
    letI := left₀
    ∀ N : NondegenerateModuleCat.{uB, v} B,
      ((@NondegenerateTensorFunctor.F A B a₀ b₀ left₀
        (@NonUnitalModule.rightRegular B b₀) hA hAB hnd).obj N).obj.carrier =
        @Tensor B B N.obj b₀ b₀.toAddCommGroup N.obj.isAddCommGroup
          (@NonUnitalModule.rightRegular B b₀) N.obj.isModule := by
  intro N
  rfl

example :
    letI := a₀
    letI := b₀
    letI := left₀
    ∀ M : NondegenerateModuleCat.{uA, v} A,
      ((@RenardHomFunctors.I A B a₀ b₀ left₀ hAB hB).obj M).obj.carrier =
        @RenardHomFunctors.inductionPart A B a₀ b₀ left₀ hAB hB
          M.obj M.obj.isAddCommGroup M.obj.isModule := by
  intro M
  rfl

end AB

section BA

variable (right₀ : letI := a₀; @NonUnitalModule Aᵐᵒᵖ B _ b₀.toAddCommGroup)
  [right₁ : NonUnitalModule Aᵐᵒᵖ B] [otherLeft : NonUnitalModule B B]
  (hBA : @ActionsCommute B A B b₀ a₀ b₀.toAddCommGroup
    (@NonUnitalModule.regular B b₀) right₀)
  (hnd : @IsNondegenerateBimodule B A B b₀ a₀ b₀.toAddCommGroup
    (@NonUnitalModule.regular B b₀) right₀)

include right₁ otherLeft

example : (inferInstance : NonUnitalModule Aᵐᵒᵖ B) = right₁ := rfl
example : (inferInstance : NonUnitalModule B B) = otherLeft := rfl

example :
    letI := a₀
    letI := b₀
    letI := right₀
    ∀ M : NondegenerateModuleCat.{uA, v} A,
      ((@NondegenerateTensorFunctor.P A B a₀ b₀
        (@NonUnitalModule.regular B b₀) right₀ hB hBA hnd).obj M).obj.isModule =
        @NonUnitalBimoduleTensor.leftModule B A b₀ a₀ B b₀.toAddCommGroup
          (@NonUnitalModule.regular B b₀) right₀ hBA M.obj
          M.obj.isAddCommGroup M.obj.isModule := by
  intro M
  rfl

example :
    letI := a₀
    letI := b₀
    letI := right₀
    ∀ N : NondegenerateModuleCat.{uB, v} B,
      ((@RenardHomFunctors.pseudoF A B a₀ b₀ right₀ hBA hA).obj N).obj.carrier =
        @RenardHomFunctors.pseudoPart A B a₀ b₀ right₀ hBA hA
          N.obj N.obj.isAddCommGroup N.obj.isModule := by
  intro N
  rfl

end BA
end CompetingStructures

/-! Regular integer interfaces use nondegenerate regular actions. -/

section Integers

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private abbrev intIdempotented := IsIdempotented.of_ring ℤ

private theorem intNondegenerate : IsNondegenerateBimodule ℤ ℤ ℤ :=
  ⟨NondegenerateTensorFunctor.regular_isNondegenerate intIdempotented,
    NondegenerateTensorFunctor.rightRegular_isNondegenerate intIdempotented⟩

private abbrev intObject : NondegenerateModuleCat.{0, 0} ℤ :=
  ⟨NonUnitalModuleCat.of ℤ ℤ,
    NondegenerateTensorFunctor.regular_isNondegenerate intIdempotented⟩

example :
    ((NondegenerateTensorFunctor.F intIdempotented
      (NonUnitalModule.regular_actionsCommute ℤ) intNondegenerate).obj intObject).obj.carrier =
      Tensor ℤ ℤ intObject.obj := rfl

example :
    ((NondegenerateTensorFunctor.P intIdempotented
      (NonUnitalModule.regular_actionsCommute ℤ) intNondegenerate).obj intObject).obj.carrier =
      Tensor ℤ ℤ intObject.obj := rfl

example : Prop :=
  letI := NondegenerateModuleCat.abelian.{0, 0} ℤ intIdempotented
  Langlands.Renard.SequenceExact
    (NondegenerateTensorFunctor.F.{0, 0, 0} intIdempotented
      (NonUnitalModule.regular_actionsCommute ℤ) intNondegenerate) ∧
  Langlands.Renard.SequenceLeftExact
    (RenardHomFunctors.I.{0, 0, 0} (NonUnitalModule.regular_actionsCommute ℤ) intIdempotented)

example : Prop :=
  letI := NondegenerateModuleCat.abelian.{0, 0} ℤ intIdempotented
  Langlands.Renard.SequenceLeftExact
    (RenardHomFunctors.pseudoF.{0, 0, 0} (NonUnitalModule.regular_actionsCommute ℤ)
      intIdempotented) ∧
  Langlands.Renard.SequenceRightExact
    (NondegenerateTensorFunctor.P.{0, 0, 0} intIdempotented
      (NonUnitalModule.regular_actionsCommute ℤ) intNondegenerate)

example : Prop :=
  letI := NondegenerateModuleCat.abelian.{0, 0} ℤ intIdempotented
  (Langlands.Renard.HomInjective intObject →
    Langlands.Renard.HomInjective
      ((RenardHomFunctors.I (NonUnitalModule.regular_actionsCommute ℤ) intIdempotented).obj
        intObject)) ∧
  (CategoryTheory.Injective intObject →
    CategoryTheory.Injective
      ((RenardHomFunctors.I (NonUnitalModule.regular_actionsCommute ℤ) intIdempotented).obj
        intObject))

end Integers

/-! Subsingleton rings and trivial modules are admitted at unrelated universes. -/

section Subsingleton

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  (hA : IsIdempotented A) (hB : IsIdempotented B)

example [Subsingleton B] [NonUnitalModule A B] :
    NondegenerateModuleCat.{uB, v} B ⥤ NondegenerateModuleCat.{uA, max uB v} A :=
  @NondegenerateTensorFunctor.F A B _ _ _ (NonUnitalModule.rightRegular B) hA
    (@actionsCommute_of_subsingleton A B B _ _ _ _ _ (NonUnitalModule.rightRegular B))
    (@isNondegenerateBimodule_of_subsingleton A B B _ _ _ _ _
      (NonUnitalModule.rightRegular B))

example [Subsingleton B] [NonUnitalModule Aᵐᵒᵖ B] :
    NondegenerateModuleCat.{uA, v} A ⥤ NondegenerateModuleCat.{uB, max uB v} B :=
  @NondegenerateTensorFunctor.P A B _ _ (NonUnitalModule.regular B) _ hB
    (@actionsCommute_of_subsingleton B A B _ _ _ _ (NonUnitalModule.regular B) _)
    (@isNondegenerateBimodule_of_subsingleton B A B _ _ _ _
      (NonUnitalModule.regular B) _)

example (M : Type v) [AddCommGroup M] [Subsingleton M] [NonUnitalModule A M] :
    NondegenerateModuleCat.{uA, v} A :=
  ⟨NonUnitalModuleCat.of A M, fun m =>
    ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ m⟩⟩

example :
    letI : NonUnitalModule A PUnit.{v + 1} := NonUnitalModule.zero
    NondegenerateModuleCat.{uA, v} A := by
  letI : NonUnitalModule A PUnit.{v + 1} := NonUnitalModule.zero
  exact ⟨NonUnitalModuleCat.of A PUnit, fun m =>
    ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ m⟩⟩

end Subsingleton

end Langlands.Algebra.NondegenerateInductionExactnessChecks
