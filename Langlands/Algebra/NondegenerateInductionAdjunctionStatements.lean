import Langlands.Algebra.NondegenerateTensorFunctor
import Langlands.Algebra.RenardHomFunctors
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Renard's actual categorical induction adjunction targets

Internal arbitrary-ring additive statements for Renard I.2.3, printed p.18 / PDF24.
The actual adjunction and all canonical correspondence data are conclusions.
-/

set_option autoImplicit false

open CategoryTheory MulOpposite

namespace Langlands.Algebra.NondegenerateInductionAdjunction

open NonUnitalModuleTensor (Tensor tmul)

universe uA uB v uC uD hC hD

/-- The canonical additive map `f ↦ l ≫ f ≫ r` on actual categorical Hom groups. -/
def compositionMap {C : Type uC} [Category.{hC} C] [Preadditive C]
    {X' X Y Y' : C} (l : X' ⟶ X) (r : Y ⟶ Y') :
    (X ⟶ Y) →+ (X' ⟶ Y') where
  toFun f := l ≫ f ≫ r
  map_zero' := by simp
  map_add' f g := by simp only [Preadditive.comp_add, Preadditive.add_comp]

/-- Whole-map coherence for the additive refinement of the same actual adjunction.
The Hom-space maps in the two naturality identities are composition maps. -/
def AdditiveAdjunctionCoherence
    {C : Type uC} {D : Type uD} [Category.{hC} C] [Category.{hD} D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R) (E : ∀ X Y, (L.obj X ⟶ Y) ≃+ (X ⟶ R.obj Y)) : Prop :=
  (∀ X Y, (E X Y).toEquiv = adj.homEquiv X Y) ∧
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
  (∀ Y : D, adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y) = 𝟙 (R.obj Y))

section FFamily

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule A B]

local instance : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : ActionsCommute A B B) (hnd : IsNondegenerateBimodule A B B)

/-- Evaluation of an actual original map into the actual B-nondegenerate Hom part. -/
def fEvaluationPairing (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A)
    (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) : B →+ N.obj →+ M.obj := by
  let g' : NonUnitalModuleHom B N.obj (RenardHomFunctors.inductionPart hAB hB M.obj) := g.hom
  exact
    { toFun := fun b =>
        { toFun := fun n => (show NonUnitalModuleHom A B M.obj from (g' n).val) b
          map_zero' := by
            exact congrArg (fun z : RenardHomFunctors.inductionPart hAB hB M.obj =>
              (show NonUnitalModuleHom A B M.obj from z.val) b) g'.map_zero
          map_add' := fun n n' => by
            exact congrArg (fun z : RenardHomFunctors.inductionPart hAB hB M.obj =>
              (show NonUnitalModuleHom A B M.obj from z.val) b) (g'.map_add n n') }
      map_zero' := by
        apply AddMonoidHom.ext
        intro n
        exact (show NonUnitalModuleHom A B M.obj from (g' n).val).map_zero
      map_add' := fun b b' => by
        apply AddMonoidHom.ext
        intro n
        exact (show NonUnitalModuleHom A B M.obj from (g' n).val).map_add b b' }

/-- Balancing follows intrinsically from g's original B-linearity and the
published source-precomposition action; no certificate is supplied. -/
theorem fEvaluationPairing_balanced (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A)
    (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) :
    NonUnitalModuleTensor.IsBalanced B (fEvaluationPairing hB hAB N M g) := by
  let g' : NonUnitalModuleHom B N.obj (RenardHomFunctors.inductionPart hAB hB M.obj) := g.hom
  intro a b n
  exact (congrArg (fun z : RenardHomFunctors.inductionPart hAB hB M.obj =>
    (show NonUnitalModuleHom A B M.obj from z.val) b) (g'.map_smul a n)).symm

/-- Package precisely the published quotient lift as an actual categorical morphism.
Its A-linearity comes from the values of g being original A-intertwiners. -/
def fUncurry (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A)
    (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) :
    (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N ⟶ M :=
  ObjectProperty.homMk
    (NonUnitalBimoduleTensor.leftLift hAB
      (fEvaluationPairing hB hAB N M g)
      (fEvaluationPairing_balanced hB hAB N M g)
      (fun a b n =>
        (show NonUnitalModuleHom A B M.obj from ((show NonUnitalModuleHom B N.obj (RenardHomFunctors.inductionPart hAB hB M.obj) from g.hom) n).val).map_smul a b))

/-- The entire underlying additive map is the original published balanced lift. -/
theorem fUncurry_toAddMonoidHom (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A)
    (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) :
    (fUncurry hA hB hAB hnd N M g).hom.toAddMonoidHom =
      NonUnitalModuleTensor.lift B (fEvaluationPairing hB hAB N M g)
        (fEvaluationPairing_balanced hB hAB N M g) := rfl

/-- The quotient-lift inverse is additive on the actual full-subcategory Hom groups. -/
def fUncurryAddHom (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A) :
    (N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) →+
      ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N ⟶ M) where
  toFun := fUncurry hA hB hAB hnd N M
  map_zero' := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext B (fun _ _ => rfl))
  map_add' g g' := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext B (fun _ _ => rfl))

/-- Canonical actual F ⊣ I, including its precise additive correspondence,
published inverse quotient lift, both inverse identities, naturality, unit and counit. -/
def CanonicalFInductionAdjunction : Prop :=
  ∃ adj : (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd) ⊣ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB),
  ∃ E : ∀ (N : NondegenerateModuleCat.{uB, max uB v} B) (M : NondegenerateModuleCat.{uA, max uB v} A),
    ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N ⟶ M) ≃+
      (N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ N M (f : (NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N ⟶ M) (n : N.obj) (b : B),
      fEvaluationPairing hB hAB N M ((E N M) f) b n =
        f.hom.toAddMonoidHom (tmul B B N.obj b n)) ∧
    (∀ N M, (E N M).symm.toAddMonoidHom = fUncurryAddHom hA hB hAB hnd N M) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M),
      ((E N M).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift B (fEvaluationPairing hB hAB N M g)
          (fEvaluationPairing_balanced hB hAB N M g)) ∧
    (∀ N M (g : N ⟶ (RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M) (b : B) (n : N.obj),
      ((E N M).symm g).hom.toAddMonoidHom (tmul B B N.obj b n) =
        fEvaluationPairing hB hAB N M g b n) ∧
    (∀ N M,
      (fUncurryAddHom hA hB hAB hnd N M).comp (E N M).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E N M).toAddMonoidHom.comp (fUncurryAddHom hA hB hAB hnd N M) =
        AddMonoidHom.id _) ∧
    (∀ (N : NondegenerateModuleCat.{uB, max uB v} B) (n : N.obj) (b : B),
      fEvaluationPairing hB hAB N ((NondegenerateTensorFunctor.F.{uA, uB, max uB v} hA hAB hnd).obj N)
        (adj.unit.app N) b n = tmul B B N.obj b n) ∧
    (∀ (M : NondegenerateModuleCat.{uA, max uB v} A) (b : B) (h : ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj),
      (adj.counit.app M).hom.toAddMonoidHom
        (tmul B B ((RenardHomFunctors.I.{uA, uB, max uB v} hAB hB).obj M).obj b h) = (show NonUnitalModuleHom A B M.obj from h.val) b)

end FFamily

section PFamily

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule Aᵐᵒᵖ B]

local instance : NonUnitalModule B B := NonUnitalModule.regular B

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hBA : ActionsCommute B A B) (hnd : IsNondegenerateBimodule B A B)

/-- Evaluation of an actual original map into the actual A-nondegenerate Hom part. -/
def pEvaluationPairing (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B)
    (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) : B →+ M.obj →+ N.obj := by
  let g' : NonUnitalModuleHom A M.obj (RenardHomFunctors.pseudoPart hBA hA N.obj) := g.hom
  exact
    { toFun := fun b =>
        { toFun := fun n => (show NonUnitalModuleHom B B N.obj from (g' n).val) b
          map_zero' := by
            exact congrArg (fun z : RenardHomFunctors.pseudoPart hBA hA N.obj =>
              (show NonUnitalModuleHom B B N.obj from z.val) b) g'.map_zero
          map_add' := fun n n' => by
            exact congrArg (fun z : RenardHomFunctors.pseudoPart hBA hA N.obj =>
              (show NonUnitalModuleHom B B N.obj from z.val) b) (g'.map_add n n') }
      map_zero' := by
        apply AddMonoidHom.ext
        intro n
        exact (show NonUnitalModuleHom B B N.obj from (g' n).val).map_zero
      map_add' := fun b b' => by
        apply AddMonoidHom.ext
        intro n
        exact (show NonUnitalModuleHom B B N.obj from (g' n).val).map_add b b' }

/-- Balancing follows intrinsically from g's original A-linearity and the
published source-precomposition action; no certificate is supplied. -/
theorem pEvaluationPairing_balanced (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B)
    (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) :
    NonUnitalModuleTensor.IsBalanced A (pEvaluationPairing hA hBA M N g) := by
  let g' : NonUnitalModuleHom A M.obj (RenardHomFunctors.pseudoPart hBA hA N.obj) := g.hom
  intro a b n
  exact (congrArg (fun z : RenardHomFunctors.pseudoPart hBA hA N.obj =>
    (show NonUnitalModuleHom B B N.obj from z.val) b) (g'.map_smul a n)).symm

/-- Package precisely the published quotient lift as an actual categorical morphism.
Its B-linearity comes from the values of g being original B-intertwiners. -/
def pUncurry (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B)
    (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) :
    (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M ⟶ N :=
  ObjectProperty.homMk
    (NonUnitalBimoduleTensor.leftLift hBA
      (pEvaluationPairing hA hBA M N g)
      (pEvaluationPairing_balanced hA hBA M N g)
      (fun a b n =>
        (show NonUnitalModuleHom B B N.obj from ((show NonUnitalModuleHom A M.obj (RenardHomFunctors.pseudoPart hBA hA N.obj) from g.hom) n).val).map_smul a b))

/-- The entire underlying additive map is the original published balanced lift. -/
theorem pUncurry_toAddMonoidHom (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B)
    (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) :
    (pUncurry hA hB hBA hnd M N g).hom.toAddMonoidHom =
      NonUnitalModuleTensor.lift A (pEvaluationPairing hA hBA M N g)
        (pEvaluationPairing_balanced hA hBA M N g) := rfl

/-- The quotient-lift inverse is additive on the actual full-subcategory Hom groups. -/
def pUncurryAddHom (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B) :
    (M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) →+
      ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M ⟶ N) where
  toFun := pUncurry hA hB hBA hnd M N
  map_zero' := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext A (fun _ _ => rfl))
  map_add' g g' := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    exact DFunLike.congr_fun (NonUnitalModuleTensor.hom_ext A (fun _ _ => rfl))

/-- Canonical actual P ⊣ pseudoF, including its precise additive correspondence,
published inverse quotient lift, both inverse identities, naturality, unit and counit. -/
def CanonicalPInductionAdjunction : Prop :=
  ∃ adj : (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd) ⊣ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA),
  ∃ E : ∀ (M : NondegenerateModuleCat.{uA, max uB v} A) (N : NondegenerateModuleCat.{uB, max uB v} B),
    ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M ⟶ N) ≃+
      (M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N),
    AdditiveAdjunctionCoherence _ _ adj E ∧
    (∀ M N (f : (NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M ⟶ N) (n : M.obj) (b : B),
      pEvaluationPairing hA hBA M N ((E M N) f) b n =
        f.hom.toAddMonoidHom (tmul A B M.obj b n)) ∧
    (∀ M N, (E M N).symm.toAddMonoidHom = pUncurryAddHom hA hB hBA hnd M N) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N),
      ((E M N).symm g).hom.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (pEvaluationPairing hA hBA M N g)
          (pEvaluationPairing_balanced hA hBA M N g)) ∧
    (∀ M N (g : M ⟶ (RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N) (b : B) (n : M.obj),
      ((E M N).symm g).hom.toAddMonoidHom (tmul A B M.obj b n) =
        pEvaluationPairing hA hBA M N g b n) ∧
    (∀ M N,
      (pUncurryAddHom hA hB hBA hnd M N).comp (E M N).toAddMonoidHom =
        AddMonoidHom.id _ ∧
      (E M N).toAddMonoidHom.comp (pUncurryAddHom hA hB hBA hnd M N) =
        AddMonoidHom.id _) ∧
    (∀ (M : NondegenerateModuleCat.{uA, max uB v} A) (n : M.obj) (b : B),
      pEvaluationPairing hA hBA M ((NondegenerateTensorFunctor.P.{uA, uB, max uB v} hB hBA hnd).obj M)
        (adj.unit.app M) b n = tmul A B M.obj b n) ∧
    (∀ (N : NondegenerateModuleCat.{uB, max uB v} B) (b : B) (h : ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj),
      (adj.counit.app N).hom.toAddMonoidHom
        (tmul A B ((RenardHomFunctors.pseudoF.{uA, uB, max uB v} hBA hA).obj N).obj b h) = (show NonUnitalModuleHom B B N.obj from h.val) b)

end PFamily

/-- Closed F-I target: only the supplied left A-action, the right regular B-action,
and the source's own nondegenerate A–B bimodule hypothesis. -/
def NondegenerateFInductionAdjunctionTheorem : Prop :=
  ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    [hLeft : NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ hLeft (NonUnitalModule.rightRegular B))
    (hnd : @IsNondegenerateBimodule A B B _ _ _ hLeft (NonUnitalModule.rightRegular B)),
    CanonicalFInductionAdjunction.{uA, uB, v} hA hB hAB hnd

/-- Closed P-pseudoF target: only the supplied right A-action, the left regular B-action,
and the source's own nondegenerate B–A bimodule hypothesis. -/
def NondegeneratePInductionAdjunctionTheorem : Prop :=
  ∀ (A : Type uA) (B : Type uB) [NonUnitalRing A] [NonUnitalRing B]
    [hRight : NonUnitalModule Aᵐᵒᵖ B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) hRight)
    (hnd : @IsNondegenerateBimodule B A B _ _ _ (NonUnitalModule.regular B) hRight),
    CanonicalPInductionAdjunction.{uA, uB, v} hA hB hBA hnd

end Langlands.Algebra.NondegenerateInductionAdjunction
