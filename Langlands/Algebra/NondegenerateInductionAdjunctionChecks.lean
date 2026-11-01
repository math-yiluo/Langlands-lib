import Langlands.Algebra.NondegenerateInductionAdjunctionStatements

/-!
# Complete declaration and boundary checks for the actual induction targets

These are interface checks and definitional equalities. They assume no target adjunction.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateInductionAdjunctionChecks

open NondegenerateInductionAdjunction
open NonUnitalModuleTensor (Tensor tmul)

universe uA uB v uC uD hC hD

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The Hom-space composition map exposes whole categorical composition. -/
example : ∀ {C : Type uC} [Category.{hC} C] [Preadditive C]
    {X' X Y Y' : C}, (X' ⟶ X) → (Y ⟶ Y') → (X ⟶ Y) →+ (X' ⟶ Y') := @compositionMap

example {C : Type uC} [Category.{hC} C] [Preadditive C]
    {X' X Y Y' : C} (l : X' ⟶ X) (r : Y ⟶ Y') (f : X ⟶ Y) :
    compositionMap l r f = l ≫ f ≫ r := rfl

example : ∀ {C : Type uC} {D : Type uD} [Category.{hC} C] [Category.{hD} D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R), (∀ X Y, (L.obj X ⟶ Y) ≃+ (X ⟶ R.obj Y)) → Prop :=
  @AdditiveAdjunctionCoherence

example
    {C : Type uC} {D : Type uD} [Category.{hC} C] [Category.{hD} D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R) (E : ∀ X Y, (L.obj X ⟶ Y) ≃+ (X ⟶ R.obj Y)) :
    AdditiveAdjunctionCoherence L R adj E =
  ((∀ X Y, (E X Y).toEquiv = adj.homEquiv X Y) ∧
  (∀ (X' X : C) (Y Y' : D) (s : X' ⟶ X) (t : Y ⟶ Y'),
    (E X' Y').toAddMonoidHom.comp (compositionMap (L.map s) t) =
      (compositionMap s (R.map t)).comp (E X Y).toAddMonoidHom) ∧
  (∀ (X' X : C) (Y Y' : D) (s : X' ⟶ X) (t : Y ⟶ Y'),
    (E X' Y').symm.toAddMonoidHom.comp (compositionMap s (R.map t)) =
      (compositionMap (L.map s) t).comp (E X Y).symm.toAddMonoidHom) ∧
  (∀ (X X' : C) (s : X ⟶ X'),
    s ≫ adj.unit.app X' = adj.unit.app X ≫ R.map (L.map s)) ∧
  (∀ (Y Y' : D) (t : Y ⟶ Y'),
    L.map (R.map t) ≫ adj.counit.app Y' = adj.counit.app Y ≫ t) ∧
  (∀ X : C, L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X) = 𝟙 (L.obj X)) ∧
  (∀ Y : D, adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y) = 𝟙 (R.obj Y))) := rfl

/-! Independent: ring universes (uA,uB), residual parameter v. -/

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hAction (NonUnitalModule.rightRegular B)) (hnd : @IsNondegenerateBimodule A B B _ _ _ hAction (NonUnitalModule.rightRegular B)), Prop := @CanonicalFInductionAdjunction.{uA, uB, v}

example : (NondegenerateFInductionAdjunctionTheorem.{uA, uB, v} : Prop) =
  (∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    [hLeft : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hLeft (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B _ _ _ hLeft (NonUnitalModule.rightRegular B)),
    CanonicalFInductionAdjunction.{uA, uB, v} hA hB hAB hnd) := rfl

section IndependentF
variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule A B]
local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

example : CanonicalFInductionAdjunction.{uA, uB, v} hA hB hAB hnd =
  (∃ adj : (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd) ⊣ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB),
  ∃ E : ∀ (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A),
    ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N ⟶ M) ≃+
      (N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ N M (f : (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N ⟶ M) (n : N.obj) (b : B),
      fEvaluationPairing.{uA, uB, v} hB hAB N M ((E N M) f) b n =
        f.hom.toAddMonoidHom (tmul B B N.obj b n)) ∧
    (∀ N M, (E N M).symm.toAddMonoidHom = fUncurryAddHom.{uA, uB, v} hA hB hAB hnd N M) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M),
      ((E N M).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift B (fEvaluationPairing.{uA, uB, v} hB hAB N M g)
          (fEvaluationPairing_balanced.{uA, uB, v} hB hAB N M g)) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) (b : B) (n : N.obj),
      ((E N M).symm g).hom.toAddMonoidHom (tmul B B N.obj b n) =
        fEvaluationPairing.{uA, uB, v} hB hAB N M g b n) ∧
    (∀ N M,
      (fUncurryAddHom.{uA, uB, v} hA hB hAB hnd N M).comp (E N M).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E N M).toAddMonoidHom.comp (fUncurryAddHom.{uA, uB, v} hA hB hAB hnd N M) =
        AddMonoidHom.id _) ∧
    (∀ (N : NondegenerateModuleCat.{uB, max uB v} B) (n : N.obj) (b : B),
      fEvaluationPairing.{uA, uB, v} hB hAB N ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N)
        (adj.unit.app N) b n = tmul B B N.obj b n) ∧
    (∀ (M : NondegenerateModuleCat.{uA, max uB v} A) (b : B) (h : ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj),
      (adj.counit.app M).hom.toAddMonoidHom
        (tmul B B ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj b h) = (show NonUnitalModuleHom A B M.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{uB, max uB v} B ⥤ NondegenerateModuleCat.{uA, max uB v} A := NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd
example : NondegenerateModuleCat.{uA, max uB v} A ⥤ NondegenerateModuleCat.{uB, max uB v} B := RenardHomFunctors.I.{uA, uB, max uB v} hAB hB
example : NondegenerateModuleCat.{uB, max uB v} B ⥤ NondegenerateModuleCat.{uB, max uB v} B := (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd) ⋙ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB)
example : NondegenerateModuleCat.{uA, max uB v} A ⥤ NondegenerateModuleCat.{uA, max uB v} A := (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB) ⋙ (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd)

example (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A) (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) (b : B) (n : N.obj) :
    fEvaluationPairing hB hAB N M g b n =
      (show NonUnitalModuleHom A B M.obj from
        ((show NonUnitalModuleHom B N.obj (RenardHomFunctors.inductionPart hAB hB M.obj) from g.hom) n).val) b := rfl

example (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A) (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) :
    (fUncurryAddHom hA hB hAB hnd N M g).hom.toAddMonoidHom =
      NonUnitalModuleTensor.lift B (fEvaluationPairing hB hAB N M g)
        (fEvaluationPairing_balanced hB hAB N M g) := rfl

example (N : NondegenerateModuleCat.{uB, max uB v} B) : ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N).obj.carrier = Tensor B B N.obj := rfl
example (N : NondegenerateModuleCat.{uB, max uB v} B) : ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N).obj.isAddCommGroup =
    NonUnitalModuleTensor.addCommGroup B B N.obj := rfl
example (N : NondegenerateModuleCat.{uB, max uB v} B) : ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N).obj.isModule =
    NonUnitalBimoduleTensor.leftModule hAB N.obj := rfl
example (M : NondegenerateModuleCat.{uA, max uB v} A) : ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj.carrier =
    RenardHomFunctors.inductionPart hAB hB M.obj := rfl
example (M : NondegenerateModuleCat.{uA, max uB v} A) : ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj.isAddCommGroup =
    (inferInstance : AddCommGroup (RenardHomFunctors.inductionPart hAB hB M.obj)) := rfl
example (M : NondegenerateModuleCat.{uA, max uB v} A) : ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj.isModule =
    (inferInstance : NonUnitalModule B (RenardHomFunctors.inductionPart hAB hB M.obj)) := rfl

example {N N' : NondegenerateModuleCat.{uB, max uB v} B} (s : N' ⟶ N) :
    ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).map s).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalModuleHom.id Bᵐᵒᵖ B) s.hom := rfl
example {M M' : NondegenerateModuleCat.{uA, max uB v} A} (t : M ⟶ M') :
    ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).map t).hom =
      (NondegenerateHomFunctor.ambientMap hAB t.hom).restrictNondegeneratePart hB := rfl

end IndependentF

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hAction) (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hAction), Prop := @CanonicalPInductionAdjunction.{uA, uB, v}

example : (NondegeneratePInductionAdjunctionTheorem.{uA, uB, v} : Prop) =
  (∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    [hRight : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hRight)
    (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hRight),
    CanonicalPInductionAdjunction.{uA, uB, v} hA hB hBA hnd) := rfl

section IndependentP
variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule Aᵐᵒᵖ B]
local instance : NonUnitalModule B B := NonUnitalModule.regular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)

example : CanonicalPInductionAdjunction.{uA, uB, v} hA hB hBA hnd =
  (∃ adj : (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd) ⊣ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA),
  ∃ E : ∀ (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B),
    ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M ⟶ N) ≃+
      (M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ M N (f : (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M ⟶ N) (n : M.obj) (b : B),
      pEvaluationPairing.{uA, uB, v} hA hBA M N ((E M N) f) b n =
        f.hom.toAddMonoidHom (tmul A B M.obj b n)) ∧
    (∀ M N, (E M N).symm.toAddMonoidHom = pUncurryAddHom.{uA, uB, v} hA hB hBA hnd M N) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N),
      ((E M N).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (pEvaluationPairing.{uA, uB, v} hA hBA M N g)
          (pEvaluationPairing_balanced.{uA, uB, v} hA hBA M N g)) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) (b : B) (n : M.obj),
      ((E M N).symm g).hom.toAddMonoidHom (tmul A B M.obj b n) =
        pEvaluationPairing.{uA, uB, v} hA hBA M N g b n) ∧
    (∀ M N,
      (pUncurryAddHom.{uA, uB, v} hA hB hBA hnd M N).comp (E M N).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E M N).toAddMonoidHom.comp (pUncurryAddHom.{uA, uB, v} hA hB hBA hnd M N) =
        AddMonoidHom.id _) ∧
    (∀ (M : NondegenerateModuleCat.{uA, max uB v} A) (n : M.obj) (b : B),
      pEvaluationPairing.{uA, uB, v} hA hBA M ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M)
        (adj.unit.app M) b n = tmul A B M.obj b n) ∧
    (∀ (N : NondegenerateModuleCat.{uB, max uB v} B) (b : B) (h : ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj),
      (adj.counit.app N).hom.toAddMonoidHom
        (tmul A B ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj b h) = (show NonUnitalModuleHom B B N.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{uA, max uB v} A ⥤ NondegenerateModuleCat.{uB, max uB v} B := NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd
example : NondegenerateModuleCat.{uB, max uB v} B ⥤ NondegenerateModuleCat.{uA, max uB v} A := RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA
example : NondegenerateModuleCat.{uA, max uB v} A ⥤ NondegenerateModuleCat.{uA, max uB v} A := (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd) ⋙ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA)
example : NondegenerateModuleCat.{uB, max uB v} B ⥤ NondegenerateModuleCat.{uB, max uB v} B := (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA) ⋙ (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd)

example (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B) (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) (b : B) (n : M.obj) :
    pEvaluationPairing hA hBA M N g b n =
      (show NonUnitalModuleHom B B N.obj from
        ((show NonUnitalModuleHom A M.obj (RenardHomFunctors.pseudoPart hBA hA N.obj) from g.hom) n).val) b := rfl

example (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B) (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) :
    (pUncurryAddHom hA hB hBA hnd M N g).hom.toAddMonoidHom =
      NonUnitalModuleTensor.lift A (pEvaluationPairing hA hBA M N g)
        (pEvaluationPairing_balanced hA hBA M N g) := rfl

example (M : NondegenerateModuleCat.{uA, max uB v} A) : ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M).obj.carrier = Tensor A B M.obj := rfl
example (M : NondegenerateModuleCat.{uA, max uB v} A) : ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M).obj.isAddCommGroup =
    NonUnitalModuleTensor.addCommGroup A B M.obj := rfl
example (M : NondegenerateModuleCat.{uA, max uB v} A) : ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M).obj.isModule =
    NonUnitalBimoduleTensor.leftModule hBA M.obj := rfl
example (N : NondegenerateModuleCat.{uB, max uB v} B) : ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj.carrier =
    RenardHomFunctors.pseudoPart hBA hA N.obj := rfl
example (N : NondegenerateModuleCat.{uB, max uB v} B) : ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj.isAddCommGroup =
    (inferInstance : AddCommGroup (RenardHomFunctors.pseudoPart hBA hA N.obj)) := rfl
example (N : NondegenerateModuleCat.{uB, max uB v} B) : ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj.isModule =
    (inferInstance : NonUnitalModule A (RenardHomFunctors.pseudoPart hBA hA N.obj)) := rfl

example {M M' : NondegenerateModuleCat.{uA, max uB v} A} (s : M' ⟶ M) :
    ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).map s).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) s.hom := rfl
example {N N' : NondegenerateModuleCat.{uB, max uB v} B} (t : N ⟶ N') :
    ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).map t).hom =
      (NondegenerateHomFunctor.ambientMap hBA t.hom).restrictNondegeneratePart hA := rfl

end IndependentP

/-! Unequal01: ring universes (0,1), residual parameter 0. -/

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hAction (NonUnitalModule.rightRegular B)) (hnd : @IsNondegenerateBimodule A B B _ _ _ hAction (NonUnitalModule.rightRegular B)), Prop := @CanonicalFInductionAdjunction.{0, 1, 0}

example : (NondegenerateFInductionAdjunctionTheorem.{0, 1, 0} : Prop) =
  (∀ (A : Type 0) (B : Type 1) [NonUnitalRing A] [NonUnitalRing B]
    [hLeft : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hLeft (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B _ _ _ hLeft (NonUnitalModule.rightRegular B)),
    CanonicalFInductionAdjunction.{0, 1, 0} hA hB hAB hnd) := rfl

section Unequal01F
variable {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule A B]
local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

example : CanonicalFInductionAdjunction.{0, 1, 0} hA hB hAB hnd =
  (∃ adj : (NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd) ⊣ (RenardHomFunctors.I.{0, 1, max 1 0} hAB hB),
  ∃ E : ∀ (N : NondegenerateModuleCat.{1, max 1 0} B) (M : NondegenerateModuleCat.{0, max 1 0} A),
    ((NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd).obj N ⟶ M) ≃+
      (N ⟶ (RenardHomFunctors.I.{0, 1, max 1 0} hAB hB).obj M),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ N M (f : (NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd).obj N ⟶ M) (n : N.obj) (b : B),
      fEvaluationPairing.{0, 1, 0} hB hAB N M ((E N M) f) b n =
        f.hom.toAddMonoidHom (tmul B B N.obj b n)) ∧
    (∀ N M, (E N M).symm.toAddMonoidHom = fUncurryAddHom.{0, 1, 0} hA hB hAB hnd N M) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{0, 1, max 1 0} hAB hB).obj M),
      ((E N M).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift B (fEvaluationPairing.{0, 1, 0} hB hAB N M g)
          (fEvaluationPairing_balanced.{0, 1, 0} hB hAB N M g)) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{0, 1, max 1 0} hAB hB).obj M) (b : B) (n : N.obj),
      ((E N M).symm g).hom.toAddMonoidHom (tmul B B N.obj b n) =
        fEvaluationPairing.{0, 1, 0} hB hAB N M g b n) ∧
    (∀ N M,
      (fUncurryAddHom.{0, 1, 0} hA hB hAB hnd N M).comp (E N M).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E N M).toAddMonoidHom.comp (fUncurryAddHom.{0, 1, 0} hA hB hAB hnd N M) =
        AddMonoidHom.id _) ∧
    (∀ (N : NondegenerateModuleCat.{1, max 1 0} B) (n : N.obj) (b : B),
      fEvaluationPairing.{0, 1, 0} hB hAB N ((NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd).obj N)
        (adj.unit.app N) b n = tmul B B N.obj b n) ∧
    (∀ (M : NondegenerateModuleCat.{0, max 1 0} A) (b : B) (h : ((RenardHomFunctors.I.{0, 1, max 1 0} hAB hB).obj M).obj),
      (adj.counit.app M).hom.toAddMonoidHom
        (tmul B B ((RenardHomFunctors.I.{0, 1, max 1 0} hAB hB).obj M).obj b h) = (show NonUnitalModuleHom A B M.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{1, max 1 0} B ⥤ NondegenerateModuleCat.{0, max 1 0} A := NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd
example : NondegenerateModuleCat.{0, max 1 0} A ⥤ NondegenerateModuleCat.{1, max 1 0} B := RenardHomFunctors.I.{0, 1, max 1 0} hAB hB
example : NondegenerateModuleCat.{1, max 1 0} B ⥤ NondegenerateModuleCat.{1, max 1 0} B := (NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd) ⋙ (RenardHomFunctors.I.{0, 1, max 1 0} hAB hB)
example : NondegenerateModuleCat.{0, max 1 0} A ⥤ NondegenerateModuleCat.{0, max 1 0} A := (RenardHomFunctors.I.{0, 1, max 1 0} hAB hB) ⋙ (NondegenerateTensorFunctor.F.{0, 1, max 1 0} hA hAB hnd)

end Unequal01F

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hAction) (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hAction), Prop := @CanonicalPInductionAdjunction.{0, 1, 0}

example : (NondegeneratePInductionAdjunctionTheorem.{0, 1, 0} : Prop) =
  (∀ (A : Type 0) (B : Type 1) [NonUnitalRing A] [NonUnitalRing B]
    [hRight : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hRight)
    (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hRight),
    CanonicalPInductionAdjunction.{0, 1, 0} hA hB hBA hnd) := rfl

section Unequal01P
variable {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule Aᵐᵒᵖ B]
local instance : NonUnitalModule B B := NonUnitalModule.regular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)

example : CanonicalPInductionAdjunction.{0, 1, 0} hA hB hBA hnd =
  (∃ adj : (NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd) ⊣ (RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA),
  ∃ E : ∀ (M : NondegenerateModuleCat.{0, max 1 0} A) (N : NondegenerateModuleCat.{1, max 1 0} B),
    ((NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd).obj M ⟶ N) ≃+
      (M ⟶ (RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA).obj N),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ M N (f : (NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd).obj M ⟶ N) (n : M.obj) (b : B),
      pEvaluationPairing.{0, 1, 0} hA hBA M N ((E M N) f) b n =
        f.hom.toAddMonoidHom (tmul A B M.obj b n)) ∧
    (∀ M N, (E M N).symm.toAddMonoidHom = pUncurryAddHom.{0, 1, 0} hA hB hBA hnd M N) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA).obj N),
      ((E M N).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (pEvaluationPairing.{0, 1, 0} hA hBA M N g)
          (pEvaluationPairing_balanced.{0, 1, 0} hA hBA M N g)) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA).obj N) (b : B) (n : M.obj),
      ((E M N).symm g).hom.toAddMonoidHom (tmul A B M.obj b n) =
        pEvaluationPairing.{0, 1, 0} hA hBA M N g b n) ∧
    (∀ M N,
      (pUncurryAddHom.{0, 1, 0} hA hB hBA hnd M N).comp (E M N).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E M N).toAddMonoidHom.comp (pUncurryAddHom.{0, 1, 0} hA hB hBA hnd M N) =
        AddMonoidHom.id _) ∧
    (∀ (M : NondegenerateModuleCat.{0, max 1 0} A) (n : M.obj) (b : B),
      pEvaluationPairing.{0, 1, 0} hA hBA M ((NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd).obj M)
        (adj.unit.app M) b n = tmul A B M.obj b n) ∧
    (∀ (N : NondegenerateModuleCat.{1, max 1 0} B) (b : B) (h : ((RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA).obj N).obj),
      (adj.counit.app N).hom.toAddMonoidHom
        (tmul A B ((RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA).obj N).obj b h) = (show NonUnitalModuleHom B B N.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{0, max 1 0} A ⥤ NondegenerateModuleCat.{1, max 1 0} B := NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd
example : NondegenerateModuleCat.{1, max 1 0} B ⥤ NondegenerateModuleCat.{0, max 1 0} A := RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA
example : NondegenerateModuleCat.{0, max 1 0} A ⥤ NondegenerateModuleCat.{0, max 1 0} A := (NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd) ⋙ (RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA)
example : NondegenerateModuleCat.{1, max 1 0} B ⥤ NondegenerateModuleCat.{1, max 1 0} B := (RenardHomFunctors.pseudoF.{0, 1, max 1 0} hBA hA) ⋙ (NondegenerateTensorFunctor.P.{0, 1, max 1 0} hB hBA hnd)

end Unequal01P

/-! Unequal10: ring universes (1,0), residual parameter 1. -/

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hAction (NonUnitalModule.rightRegular B)) (hnd : @IsNondegenerateBimodule A B B _ _ _ hAction (NonUnitalModule.rightRegular B)), Prop := @CanonicalFInductionAdjunction.{1, 0, 1}

example : (NondegenerateFInductionAdjunctionTheorem.{1, 0, 1} : Prop) =
  (∀ (A : Type 1) (B : Type 0) [NonUnitalRing A] [NonUnitalRing B]
    [hLeft : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hLeft (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B _ _ _ hLeft (NonUnitalModule.rightRegular B)),
    CanonicalFInductionAdjunction.{1, 0, 1} hA hB hAB hnd) := rfl

section Unequal10F
variable {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule A B]
local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

example : CanonicalFInductionAdjunction.{1, 0, 1} hA hB hAB hnd =
  (∃ adj : (NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd) ⊣ (RenardHomFunctors.I.{1, 0, max 0 1} hAB hB),
  ∃ E : ∀ (N : NondegenerateModuleCat.{0, max 0 1} B) (M : NondegenerateModuleCat.{1, max 0 1} A),
    ((NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd).obj N ⟶ M) ≃+
      (N ⟶ (RenardHomFunctors.I.{1, 0, max 0 1} hAB hB).obj M),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ N M (f : (NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd).obj N ⟶ M) (n : N.obj) (b : B),
      fEvaluationPairing.{1, 0, 1} hB hAB N M ((E N M) f) b n =
        f.hom.toAddMonoidHom (tmul B B N.obj b n)) ∧
    (∀ N M, (E N M).symm.toAddMonoidHom = fUncurryAddHom.{1, 0, 1} hA hB hAB hnd N M) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{1, 0, max 0 1} hAB hB).obj M),
      ((E N M).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift B (fEvaluationPairing.{1, 0, 1} hB hAB N M g)
          (fEvaluationPairing_balanced.{1, 0, 1} hB hAB N M g)) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{1, 0, max 0 1} hAB hB).obj M) (b : B) (n : N.obj),
      ((E N M).symm g).hom.toAddMonoidHom (tmul B B N.obj b n) =
        fEvaluationPairing.{1, 0, 1} hB hAB N M g b n) ∧
    (∀ N M,
      (fUncurryAddHom.{1, 0, 1} hA hB hAB hnd N M).comp (E N M).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E N M).toAddMonoidHom.comp (fUncurryAddHom.{1, 0, 1} hA hB hAB hnd N M) =
        AddMonoidHom.id _) ∧
    (∀ (N : NondegenerateModuleCat.{0, max 0 1} B) (n : N.obj) (b : B),
      fEvaluationPairing.{1, 0, 1} hB hAB N ((NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd).obj N)
        (adj.unit.app N) b n = tmul B B N.obj b n) ∧
    (∀ (M : NondegenerateModuleCat.{1, max 0 1} A) (b : B) (h : ((RenardHomFunctors.I.{1, 0, max 0 1} hAB hB).obj M).obj),
      (adj.counit.app M).hom.toAddMonoidHom
        (tmul B B ((RenardHomFunctors.I.{1, 0, max 0 1} hAB hB).obj M).obj b h) = (show NonUnitalModuleHom A B M.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{0, max 0 1} B ⥤ NondegenerateModuleCat.{1, max 0 1} A := NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd
example : NondegenerateModuleCat.{1, max 0 1} A ⥤ NondegenerateModuleCat.{0, max 0 1} B := RenardHomFunctors.I.{1, 0, max 0 1} hAB hB
example : NondegenerateModuleCat.{0, max 0 1} B ⥤ NondegenerateModuleCat.{0, max 0 1} B := (NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd) ⋙ (RenardHomFunctors.I.{1, 0, max 0 1} hAB hB)
example : NondegenerateModuleCat.{1, max 0 1} A ⥤ NondegenerateModuleCat.{1, max 0 1} A := (RenardHomFunctors.I.{1, 0, max 0 1} hAB hB) ⋙ (NondegenerateTensorFunctor.F.{1, 0, max 0 1} hA hAB hnd)

end Unequal10F

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hAction) (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hAction), Prop := @CanonicalPInductionAdjunction.{1, 0, 1}

example : (NondegeneratePInductionAdjunctionTheorem.{1, 0, 1} : Prop) =
  (∀ (A : Type 1) (B : Type 0) [NonUnitalRing A] [NonUnitalRing B]
    [hRight : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hRight)
    (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hRight),
    CanonicalPInductionAdjunction.{1, 0, 1} hA hB hBA hnd) := rfl

section Unequal10P
variable {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule Aᵐᵒᵖ B]
local instance : NonUnitalModule B B := NonUnitalModule.regular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)

example : CanonicalPInductionAdjunction.{1, 0, 1} hA hB hBA hnd =
  (∃ adj : (NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd) ⊣ (RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA),
  ∃ E : ∀ (M : NondegenerateModuleCat.{1, max 0 1} A) (N : NondegenerateModuleCat.{0, max 0 1} B),
    ((NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd).obj M ⟶ N) ≃+
      (M ⟶ (RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA).obj N),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ M N (f : (NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd).obj M ⟶ N) (n : M.obj) (b : B),
      pEvaluationPairing.{1, 0, 1} hA hBA M N ((E M N) f) b n =
        f.hom.toAddMonoidHom (tmul A B M.obj b n)) ∧
    (∀ M N, (E M N).symm.toAddMonoidHom = pUncurryAddHom.{1, 0, 1} hA hB hBA hnd M N) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA).obj N),
      ((E M N).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (pEvaluationPairing.{1, 0, 1} hA hBA M N g)
          (pEvaluationPairing_balanced.{1, 0, 1} hA hBA M N g)) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA).obj N) (b : B) (n : M.obj),
      ((E M N).symm g).hom.toAddMonoidHom (tmul A B M.obj b n) =
        pEvaluationPairing.{1, 0, 1} hA hBA M N g b n) ∧
    (∀ M N,
      (pUncurryAddHom.{1, 0, 1} hA hB hBA hnd M N).comp (E M N).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E M N).toAddMonoidHom.comp (pUncurryAddHom.{1, 0, 1} hA hB hBA hnd M N) =
        AddMonoidHom.id _) ∧
    (∀ (M : NondegenerateModuleCat.{1, max 0 1} A) (n : M.obj) (b : B),
      pEvaluationPairing.{1, 0, 1} hA hBA M ((NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd).obj M)
        (adj.unit.app M) b n = tmul A B M.obj b n) ∧
    (∀ (N : NondegenerateModuleCat.{0, max 0 1} B) (b : B) (h : ((RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA).obj N).obj),
      (adj.counit.app N).hom.toAddMonoidHom
        (tmul A B ((RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA).obj N).obj b h) = (show NonUnitalModuleHom B B N.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{1, max 0 1} A ⥤ NondegenerateModuleCat.{0, max 0 1} B := NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd
example : NondegenerateModuleCat.{0, max 0 1} B ⥤ NondegenerateModuleCat.{1, max 0 1} A := RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA
example : NondegenerateModuleCat.{1, max 0 1} A ⥤ NondegenerateModuleCat.{1, max 0 1} A := (NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd) ⋙ (RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA)
example : NondegenerateModuleCat.{0, max 0 1} B ⥤ NondegenerateModuleCat.{0, max 0 1} B := (RenardHomFunctors.pseudoF.{1, 0, max 0 1} hBA hA) ⋙ (NondegenerateTensorFunctor.P.{1, 0, max 0 1} hB hBA hnd)

end Unequal10P

/-! RingAboveCarrier: ring universes (1,0), residual parameter 0. -/

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hAction (NonUnitalModule.rightRegular B)) (hnd : @IsNondegenerateBimodule A B B _ _ _ hAction (NonUnitalModule.rightRegular B)), Prop := @CanonicalFInductionAdjunction.{1, 0, 0}

example : (NondegenerateFInductionAdjunctionTheorem.{1, 0, 0} : Prop) =
  (∀ (A : Type 1) (B : Type 0) [NonUnitalRing A] [NonUnitalRing B]
    [hLeft : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hLeft (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B _ _ _ hLeft (NonUnitalModule.rightRegular B)),
    CanonicalFInductionAdjunction.{1, 0, 0} hA hB hAB hnd) := rfl

section RingAboveCarrierF
variable {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule A B]
local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

example : CanonicalFInductionAdjunction.{1, 0, 0} hA hB hAB hnd =
  (∃ adj : (NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd) ⊣ (RenardHomFunctors.I.{1, 0, max 0 0} hAB hB),
  ∃ E : ∀ (N : NondegenerateModuleCat.{0, max 0 0} B) (M : NondegenerateModuleCat.{1, max 0 0} A),
    ((NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd).obj N ⟶ M) ≃+
      (N ⟶ (RenardHomFunctors.I.{1, 0, max 0 0} hAB hB).obj M),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ N M (f : (NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd).obj N ⟶ M) (n : N.obj) (b : B),
      fEvaluationPairing.{1, 0, 0} hB hAB N M ((E N M) f) b n =
        f.hom.toAddMonoidHom (tmul B B N.obj b n)) ∧
    (∀ N M, (E N M).symm.toAddMonoidHom = fUncurryAddHom.{1, 0, 0} hA hB hAB hnd N M) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{1, 0, max 0 0} hAB hB).obj M),
      ((E N M).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift B (fEvaluationPairing.{1, 0, 0} hB hAB N M g)
          (fEvaluationPairing_balanced.{1, 0, 0} hB hAB N M g)) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{1, 0, max 0 0} hAB hB).obj M) (b : B) (n : N.obj),
      ((E N M).symm g).hom.toAddMonoidHom (tmul B B N.obj b n) =
        fEvaluationPairing.{1, 0, 0} hB hAB N M g b n) ∧
    (∀ N M,
      (fUncurryAddHom.{1, 0, 0} hA hB hAB hnd N M).comp (E N M).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E N M).toAddMonoidHom.comp (fUncurryAddHom.{1, 0, 0} hA hB hAB hnd N M) =
        AddMonoidHom.id _) ∧
    (∀ (N : NondegenerateModuleCat.{0, max 0 0} B) (n : N.obj) (b : B),
      fEvaluationPairing.{1, 0, 0} hB hAB N ((NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd).obj N)
        (adj.unit.app N) b n = tmul B B N.obj b n) ∧
    (∀ (M : NondegenerateModuleCat.{1, max 0 0} A) (b : B) (h : ((RenardHomFunctors.I.{1, 0, max 0 0} hAB hB).obj M).obj),
      (adj.counit.app M).hom.toAddMonoidHom
        (tmul B B ((RenardHomFunctors.I.{1, 0, max 0 0} hAB hB).obj M).obj b h) = (show NonUnitalModuleHom A B M.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{0, max 0 0} B ⥤ NondegenerateModuleCat.{1, max 0 0} A := NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd
example : NondegenerateModuleCat.{1, max 0 0} A ⥤ NondegenerateModuleCat.{0, max 0 0} B := RenardHomFunctors.I.{1, 0, max 0 0} hAB hB
example : NondegenerateModuleCat.{0, max 0 0} B ⥤ NondegenerateModuleCat.{0, max 0 0} B := (NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd) ⋙ (RenardHomFunctors.I.{1, 0, max 0 0} hAB hB)
example : NondegenerateModuleCat.{1, max 0 0} A ⥤ NondegenerateModuleCat.{1, max 0 0} A := (RenardHomFunctors.I.{1, 0, max 0 0} hAB hB) ⋙ (NondegenerateTensorFunctor.F.{1, 0, max 0 0} hA hAB hnd)

end RingAboveCarrierF

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [hAction : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hAction) (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hAction), Prop := @CanonicalPInductionAdjunction.{1, 0, 0}

example : (NondegeneratePInductionAdjunctionTheorem.{1, 0, 0} : Prop) =
  (∀ (A : Type 1) (B : Type 0) [NonUnitalRing A] [NonUnitalRing B]
    [hRight : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hRight)
    (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hRight),
    CanonicalPInductionAdjunction.{1, 0, 0} hA hB hBA hnd) := rfl

section RingAboveCarrierP
variable {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
  [hAction : NonUnitalModule Aᵐᵒᵖ B]
local instance : NonUnitalModule B B := NonUnitalModule.regular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)

example : CanonicalPInductionAdjunction.{1, 0, 0} hA hB hBA hnd =
  (∃ adj : (NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd) ⊣ (RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA),
  ∃ E : ∀ (M : NondegenerateModuleCat.{1, max 0 0} A) (N : NondegenerateModuleCat.{0, max 0 0} B),
    ((NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd).obj M ⟶ N) ≃+
      (M ⟶ (RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA).obj N),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ M N (f : (NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd).obj M ⟶ N) (n : M.obj) (b : B),
      pEvaluationPairing.{1, 0, 0} hA hBA M N ((E M N) f) b n =
        f.hom.toAddMonoidHom (tmul A B M.obj b n)) ∧
    (∀ M N, (E M N).symm.toAddMonoidHom = pUncurryAddHom.{1, 0, 0} hA hB hBA hnd M N) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA).obj N),
      ((E M N).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (pEvaluationPairing.{1, 0, 0} hA hBA M N g)
          (pEvaluationPairing_balanced.{1, 0, 0} hA hBA M N g)) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA).obj N) (b : B) (n : M.obj),
      ((E M N).symm g).hom.toAddMonoidHom (tmul A B M.obj b n) =
        pEvaluationPairing.{1, 0, 0} hA hBA M N g b n) ∧
    (∀ M N,
      (pUncurryAddHom.{1, 0, 0} hA hB hBA hnd M N).comp (E M N).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E M N).toAddMonoidHom.comp (pUncurryAddHom.{1, 0, 0} hA hB hBA hnd M N) =
        AddMonoidHom.id _) ∧
    (∀ (M : NondegenerateModuleCat.{1, max 0 0} A) (n : M.obj) (b : B),
      pEvaluationPairing.{1, 0, 0} hA hBA M ((NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd).obj M)
        (adj.unit.app M) b n = tmul A B M.obj b n) ∧
    (∀ (N : NondegenerateModuleCat.{0, max 0 0} B) (b : B) (h : ((RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA).obj N).obj),
      (adj.counit.app N).hom.toAddMonoidHom
        (tmul A B ((RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA).obj N).obj b h) = (show NonUnitalModuleHom B B N.obj from h.val) b)) := rfl

example : NondegenerateModuleCat.{1, max 0 0} A ⥤ NondegenerateModuleCat.{0, max 0 0} B := NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd
example : NondegenerateModuleCat.{0, max 0 0} B ⥤ NondegenerateModuleCat.{1, max 0 0} A := RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA
example : NondegenerateModuleCat.{1, max 0 0} A ⥤ NondegenerateModuleCat.{1, max 0 0} A := (NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd) ⋙ (RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA)
example : NondegenerateModuleCat.{0, max 0 0} B ⥤ NondegenerateModuleCat.{0, max 0 0} B := (RenardHomFunctors.pseudoF.{1, 0, max 0 0} hBA hA) ⋙ (NondegenerateTensorFunctor.P.{1, 0, max 0 0} hB hBA hnd)

end RingAboveCarrierP

/-- Select the published subtype group before unrelated instances are introduced. -/
private abbrev originalSubmoduleGroup {R : Type uA} [NonUnitalRing R]
    {M : Type v} [AddCommGroup M] [NonUnitalModule R M]
    (S : NonUnitalSubmodule R M) : AddCommGroup S := inferInstance

/-- Select the published restricted action before unrelated instances are introduced. -/
private abbrev originalSubmoduleAction {R : Type uA} [NonUnitalRing R]
    {M : Type v} [AddCommGroup M] [NonUnitalModule R M]
    (S : NonUnitalSubmodule R M) : NonUnitalModule R S := inferInstance

/-! F: explicit original choices survive competing instances on the same carriers. -/
section CompetingF
set_option linter.overlappingInstances false
variable {A : Type uA} {B : Type uB}
  (a₀ : NonUnitalRing A) [a₁ : NonUnitalRing A]
  (b₀ : NonUnitalRing B) [b₁ : NonUnitalRing B]
variable (action₀ : @NonUnitalModule A B a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)))
  [otherAction : @NonUnitalModule A B a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀))]
  [otherBGroup : AddCommGroup B]
  (hA : @IsIdempotented A a₀) (hB : @IsIdempotented B b₀)
  (h : @ActionsCommute A B B a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) action₀ (@NonUnitalModule.rightRegular B b₀))
  (hnd : @IsNondegenerateBimodule A B B a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) action₀ (@NonUnitalModule.rightRegular B b₀))
  (X : @NondegenerateModuleCat.{uB, max uB v} B b₀)
  (Y : @NondegenerateModuleCat.{uA, max uB v} A a₀)

variable [otherXGroup : AddCommGroup (@NonUnitalModuleCat.carrier B b₀ X.obj)] [otherYGroup : AddCommGroup (@NonUnitalModuleCat.carrier A a₀ Y.obj)]
  [otherXAction : @NonUnitalModule B (@NonUnitalModuleCat.carrier B b₀ X.obj) b₀ (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj)]
  [otherYAction : @NonUnitalModule A (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj)]
  [otherTensorGroup : AddCommGroup (@Tensor B B (@NonUnitalModuleCat.carrier B b₀ X.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj) (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule B b₀ X.obj))]
  [otherTensorAction : @NonUnitalModule A (@Tensor B B (@NonUnitalModuleCat.carrier B b₀ X.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj) (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule B b₀ X.obj)) a₀ (@NonUnitalModuleTensor.addCommGroup B B (@NonUnitalModuleCat.carrier B b₀ X.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj) (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule B b₀ X.obj))]
  [otherHomGroup : AddCommGroup (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj))]
  [otherHomAction : @NonUnitalModule B (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) b₀ (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj))]
  [otherPartGroup : AddCommGroup (@nondegeneratePart B b₀ hB (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h))]
  [otherPartAction : @NonUnitalModule B (@nondegeneratePart B b₀ hB (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h)) b₀ (@originalSubmoduleGroup B b₀ (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h) (@nondegeneratePart B b₀ hB (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h)))]

include a₁ b₁ otherAction otherBGroup otherXGroup otherYGroup otherXAction otherYAction
  otherTensorGroup otherTensorAction otherHomGroup otherHomAction otherPartGroup otherPartAction

example : Prop :=
  @CanonicalFInductionAdjunction.{uA, uB, v} A B a₀ b₀ action₀ hA hB h hnd
example : @NondegenerateModuleCat.{uB, max uB v} B b₀ ⥤
    @NondegenerateModuleCat.{uA, max uB v} A a₀ := (@NondegenerateTensorFunctor.F.{uA, uB, max uB v} A B a₀ b₀ action₀ (@NonUnitalModule.rightRegular B b₀) hA h hnd)
example : @NondegenerateModuleCat.{uA, max uB v} A a₀ ⥤
    @NondegenerateModuleCat.{uB, max uB v} B b₀ := (@RenardHomFunctors.I.{uA, uB, max uB v} A B a₀ b₀ action₀ h hB)
example : @NonUnitalModuleCat.carrier A a₀ (((@NondegenerateTensorFunctor.F.{uA, uB, max uB v} A B a₀ b₀ action₀ (@NonUnitalModule.rightRegular B b₀) hA h hnd)).obj X).obj = (@Tensor B B (@NonUnitalModuleCat.carrier B b₀ X.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj) (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule B b₀ X.obj)) := rfl
example : @NonUnitalModuleCat.isAddCommGroup A a₀ (((@NondegenerateTensorFunctor.F.{uA, uB, max uB v} A B a₀ b₀ action₀ (@NonUnitalModule.rightRegular B b₀) hA h hnd)).obj X).obj = (@NonUnitalModuleTensor.addCommGroup B B (@NonUnitalModuleCat.carrier B b₀ X.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj) (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule B b₀ X.obj)) := rfl
example : @NonUnitalModuleCat.isModule A a₀ (((@NondegenerateTensorFunctor.F.{uA, uB, max uB v} A B a₀ b₀ action₀ (@NonUnitalModule.rightRegular B b₀) hA h hnd)).obj X).obj = (@NonUnitalBimoduleTensor.leftModule A B a₀ b₀ B (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) action₀ (@NonUnitalModule.rightRegular B b₀) h (@NonUnitalModuleCat.carrier B b₀ X.obj) (@NonUnitalModuleCat.isAddCommGroup B b₀ X.obj) (@NonUnitalModuleCat.isModule B b₀ X.obj)) := rfl
example : @NonUnitalModuleCat.carrier B b₀ (((@RenardHomFunctors.I.{uA, uB, max uB v} A B a₀ b₀ action₀ h hB)).obj Y).obj = (@nondegeneratePart B b₀ hB (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h)) := rfl
example : @NonUnitalModuleCat.isAddCommGroup B b₀ (((@RenardHomFunctors.I.{uA, uB, max uB v} A B a₀ b₀ action₀ h hB)).obj Y).obj = (@originalSubmoduleGroup B b₀ (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h) (@nondegeneratePart B b₀ hB (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h))) := rfl
example : @NonUnitalModuleCat.isModule B b₀ (((@RenardHomFunctors.I.{uA, uB, max uB v} A B a₀ b₀ action₀ h hB)).obj Y).obj = (@originalSubmoduleAction B b₀ (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h) (@nondegeneratePart B b₀ hB (@NonUnitalModuleHom A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup A B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction A B B (@NonUnitalModuleCat.carrier A a₀ Y.obj) a₀ b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ Y.obj) action₀ (@NonUnitalModule.rightRegular B b₀) (@NonUnitalModuleCat.isModule A a₀ Y.obj) h))) := rfl

end CompetingF

/-! P: explicit original choices survive competing instances on the same carriers. -/
section CompetingP
set_option linter.overlappingInstances false
variable {A : Type uA} {B : Type uB}
  (a₀ : NonUnitalRing A) [a₁ : NonUnitalRing A]
  (b₀ : NonUnitalRing B) [b₁ : NonUnitalRing B]
variable (action₀ : @NonUnitalModule Aᵐᵒᵖ B (@MulOpposite.instNonUnitalRing A a₀) (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)))
  [otherAction : @NonUnitalModule Aᵐᵒᵖ B (@MulOpposite.instNonUnitalRing A a₀) (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀))]
  [otherBGroup : AddCommGroup B]
  (hA : @IsIdempotented A a₀) (hB : @IsIdempotented B b₀)
  (h : @ActionsCommute B A B b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModule.regular B b₀) action₀)
  (hnd : @IsNondegenerateBimodule B A B b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModule.regular B b₀) action₀)
  (X : @NondegenerateModuleCat.{uA, max uB v} A a₀)
  (Y : @NondegenerateModuleCat.{uB, max uB v} B b₀)

variable [otherXGroup : AddCommGroup (@NonUnitalModuleCat.carrier A a₀ X.obj)] [otherYGroup : AddCommGroup (@NonUnitalModuleCat.carrier B b₀ Y.obj)]
  [otherXAction : @NonUnitalModule A (@NonUnitalModuleCat.carrier A a₀ X.obj) a₀ (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj)]
  [otherYAction : @NonUnitalModule B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj)]
  [otherTensorGroup : AddCommGroup (@Tensor A B (@NonUnitalModuleCat.carrier A a₀ X.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ X.obj))]
  [otherTensorAction : @NonUnitalModule B (@Tensor A B (@NonUnitalModuleCat.carrier A a₀ X.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ X.obj)) b₀ (@NonUnitalModuleTensor.addCommGroup A B (@NonUnitalModuleCat.carrier A a₀ X.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ X.obj))]
  [otherHomGroup : AddCommGroup (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj))]
  [otherHomAction : @NonUnitalModule A (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) a₀ (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj))]
  [otherPartGroup : AddCommGroup (@nondegeneratePart A a₀ hA (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h))]
  [otherPartAction : @NonUnitalModule A (@nondegeneratePart A a₀ hA (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h)) a₀ (@originalSubmoduleGroup A a₀ (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h) (@nondegeneratePart A a₀ hA (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h)))]

include a₁ b₁ otherAction otherBGroup otherXGroup otherYGroup otherXAction otherYAction
  otherTensorGroup otherTensorAction otherHomGroup otherHomAction otherPartGroup otherPartAction

example : Prop :=
  @CanonicalPInductionAdjunction.{uA, uB, v} A B a₀ b₀ action₀ hA hB h hnd
example : @NondegenerateModuleCat.{uA, max uB v} A a₀ ⥤
    @NondegenerateModuleCat.{uB, max uB v} B b₀ := (@NondegenerateTensorFunctor.P.{uA, uB, max uB v} A B a₀ b₀ (@NonUnitalModule.regular B b₀) action₀ hB h hnd)
example : @NondegenerateModuleCat.{uB, max uB v} B b₀ ⥤
    @NondegenerateModuleCat.{uA, max uB v} A a₀ := (@RenardHomFunctors.pseudoF.{uA, uB, max uB v} A B a₀ b₀ action₀ h hA)
example : @NonUnitalModuleCat.carrier B b₀ (((@NondegenerateTensorFunctor.P.{uA, uB, max uB v} A B a₀ b₀ (@NonUnitalModule.regular B b₀) action₀ hB h hnd)).obj X).obj = (@Tensor A B (@NonUnitalModuleCat.carrier A a₀ X.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ X.obj)) := rfl
example : @NonUnitalModuleCat.isAddCommGroup B b₀ (((@NondegenerateTensorFunctor.P.{uA, uB, max uB v} A B a₀ b₀ (@NonUnitalModule.regular B b₀) action₀ hB h hnd)).obj X).obj = (@NonUnitalModuleTensor.addCommGroup A B (@NonUnitalModuleCat.carrier A a₀ X.obj) a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj) action₀ (@NonUnitalModuleCat.isModule A a₀ X.obj)) := rfl
example : @NonUnitalModuleCat.isModule B b₀ (((@NondegenerateTensorFunctor.P.{uA, uB, max uB v} A B a₀ b₀ (@NonUnitalModule.regular B b₀) action₀ hB h hnd)).obj X).obj = (@NonUnitalBimoduleTensor.leftModule B A b₀ a₀ B (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModule.regular B b₀) action₀ h (@NonUnitalModuleCat.carrier A a₀ X.obj) (@NonUnitalModuleCat.isAddCommGroup A a₀ X.obj) (@NonUnitalModuleCat.isModule A a₀ X.obj)) := rfl
example : @NonUnitalModuleCat.carrier A a₀ (((@RenardHomFunctors.pseudoF.{uA, uB, max uB v} A B a₀ b₀ action₀ h hA)).obj Y).obj = (@nondegeneratePart A a₀ hA (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h)) := rfl
example : @NonUnitalModuleCat.isAddCommGroup A a₀ (((@RenardHomFunctors.pseudoF.{uA, uB, max uB v} A B a₀ b₀ action₀ h hA)).obj Y).obj = (@originalSubmoduleGroup A a₀ (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h) (@nondegeneratePart A a₀ hA (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h))) := rfl
example : @NonUnitalModuleCat.isModule A a₀ (((@RenardHomFunctors.pseudoF.{uA, uB, max uB v} A B a₀ b₀ action₀ h hA)).obj Y).obj = (@originalSubmoduleAction A a₀ (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h) (@nondegeneratePart A a₀ hA (@NonUnitalModuleHom B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalModuleHom.instAddCommGroup B B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) (@NonUnitalModuleCat.isModule B b₀ Y.obj)) (@NonUnitalBimoduleHomActions.sourceAction B A B (@NonUnitalModuleCat.carrier B b₀ Y.obj) b₀ a₀ (@NonUnitalNonAssocRing.toAddCommGroup B (@NonUnitalRing.toNonUnitalNonAssocRing B b₀)) (@NonUnitalModuleCat.isAddCommGroup B b₀ Y.obj) (@NonUnitalModule.regular B b₀) action₀ (@NonUnitalModuleCat.isModule B b₀ Y.obj) h))) := rfl

end CompetingP

/-! Regular integer actions: the targets and their prescribed inverse lifts specialize
without assuming an adjunction. -/

section IntegerRegular

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private abbrev intIdempotented := IsIdempotented.of_ring ℤ
private theorem intCommute : ActionsCommute ℤ ℤ ℤ :=
  NonUnitalModule.regular_actionsCommute ℤ
private theorem intNondegenerate : IsNondegenerateBimodule ℤ ℤ ℤ :=
  ⟨NondegenerateTensorFunctor.regular_isNondegenerate intIdempotented,
    NondegenerateTensorFunctor.rightRegular_isNondegenerate intIdempotented⟩
private def integerObject : NondegenerateModuleCat.{0, 0} ℤ :=
  ⟨NonUnitalModuleCat.of ℤ ℤ, intNondegenerate.1⟩

example : Prop :=
  CanonicalFInductionAdjunction.{0, 0, 0}
    intIdempotented intIdempotented intCommute intNondegenerate
example : Prop :=
  CanonicalPInductionAdjunction.{0, 0, 0}
    intIdempotented intIdempotented intCommute intNondegenerate

example (g : integerObject ⟶
    (RenardHomFunctors.I intCommute intIdempotented).obj integerObject) (b n : ℤ) :
    (fUncurryAddHom intIdempotented intIdempotented intCommute intNondegenerate
      integerObject integerObject g).hom.toAddMonoidHom (tmul ℤ ℤ ℤ b n) =
        fEvaluationPairing intIdempotented intCommute integerObject integerObject g b n := rfl

example (g : integerObject ⟶
    (RenardHomFunctors.pseudoF intCommute intIdempotented).obj integerObject) (b n : ℤ) :
    (pUncurryAddHom intIdempotented intIdempotented intCommute intNondegenerate
      integerObject integerObject g).hom.toAddMonoidHom (tmul ℤ ℤ ℤ b n) =
        pEvaluationPairing intIdempotented intCommute integerObject integerObject g b n := rfl

example (n : ℤ) :
    ((2 : ℤ) • (tmul ℤ ℤ ℤ 1 n :
      ((NondegenerateTensorFunctor.F intIdempotented intCommute intNondegenerate).obj
        integerObject).obj)) = tmul ℤ ℤ ℤ 2 n := rfl

example (n : ℤ) :
    ((2 : ℤ) • (tmul ℤ ℤ ℤ 1 n :
      ((NondegenerateTensorFunctor.P intIdempotented intCommute intNondegenerate).obj
        integerObject).obj)) = tmul ℤ ℤ ℤ 2 n := rfl

end IntegerRegular

/-! Subsingleton rings and trivial original modules are admissible interfaces. -/

section SubsingletonF
variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B] [Subsingleton B]
local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)

example : Prop := CanonicalFInductionAdjunction.{uA, uB, v} hA hB
  actionsCommute_of_subsingleton isNondegenerateBimodule_of_subsingleton

example (M : NondegenerateModuleCat.{uA, max uB v} A) :
    Subsingleton (((RenardHomFunctors.I.{uA, uB, max uB v}
      actionsCommute_of_subsingleton hB).obj M).obj) := by
  change Subsingleton (RenardHomFunctors.inductionPart actionsCommute_of_subsingleton hB M.obj)
  have h : Subsingleton (NonUnitalModuleHom A B M.obj) :=
    NonUnitalBimoduleHomActions.hom_subsingleton_of_source
  exact ⟨fun f g => Subtype.ext (h.elim f.val g.val)⟩

end SubsingletonF

section SubsingletonP
variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule Aᵐᵒᵖ B] [Subsingleton B]
local instance : NonUnitalModule B B := NonUnitalModule.regular B
variable (hA : IsIdempotented A) (hB : IsIdempotented B)

example : Prop := CanonicalPInductionAdjunction.{uA, uB, v} hA hB
  actionsCommute_of_subsingleton isNondegenerateBimodule_of_subsingleton

example (N : NondegenerateModuleCat.{uB, max uB v} B) :
    Subsingleton (((RenardHomFunctors.pseudoF.{uA, uB, max uB v}
      actionsCommute_of_subsingleton hA).obj N).obj) := by
  change Subsingleton (RenardHomFunctors.pseudoPart actionsCommute_of_subsingleton hA N.obj)
  have h : Subsingleton (NonUnitalModuleHom B B N.obj) :=
    NonUnitalBimoduleHomActions.hom_subsingleton_of_source
  exact ⟨fun f g => Subtype.ext (h.elim f.val g.val)⟩

end SubsingletonP

section TrivialModules
variable {A : Type uA} [NonUnitalRing A] (M : Type v) [AddCommGroup M]
  [NonUnitalModule A M] [Subsingleton M]

example : NondegenerateModuleCat.{uA, v} A :=
  ⟨NonUnitalModuleCat.of A M,
    fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩⟩

end TrivialModules

end Langlands.Algebra.NondegenerateInductionAdjunctionChecks
