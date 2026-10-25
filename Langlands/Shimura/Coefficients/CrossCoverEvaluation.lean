import Langlands.Shimura.Coefficients.CrossCover
import Langlands.Shimura.Coefficients.TrivializationFromSplitting

noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R]

/-- Evaluate cover sections at a lift composed with a fixed map to the cover. -/
def productEvaluationAlong {Y Z : C} (a : Z ⟶ Y) (F : Sheaf J (ModuleCat.{u} R)) :
    (J.overPullback (ModuleCat.{u} R) Z).obj ((productSheaf J Y).obj F) ⟶
      (J.overPullback (ModuleCat.{u} R) Z).obj F where
  hom.app U := F.obj.map (prod.lift (U.unop.hom ≫ a) (𝟙 U.unop.left)).op
  hom.naturality := by
    intro U V f
    change F.obj.map (prod.map (𝟙 Y) f.unop.left).op ≫
        F.obj.map (prod.lift (V.unop.hom ≫ a) (𝟙 V.unop.left)).op =
      F.obj.map (prod.lift (U.unop.hom ≫ a) (𝟙 U.unop.left)).op ≫
        F.obj.map f.unop.left.op
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
    congr 2
    apply prod.hom_ext <;> simp [Over.w f.unop, ← Category.assoc]

@[reassoc] theorem productEvaluationAlong_natural {Y Z : C} (a : Z ⟶ Y)
    {F E : Sheaf J (ModuleCat.{u} R)} (c : F ⟶ E) :
    (J.overPullback (ModuleCat.{u} R) Z).map ((productSheaf J Y).map c) ≫
        productEvaluationAlong J a E =
      productEvaluationAlong J a F ≫ (J.overPullback (ModuleCat.{u} R) Z).map c := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  exact (c.hom.naturality _).symm

variable {G H : Type u} [Group G] [Group H]

@[simp] theorem productEvaluationAlong_id (Y : Action C G)
    (F : Sheaf J (ModuleCat.{u} R)) :
    productEvaluationAlong J (𝟙 Y.V) F = productEvaluation J Y F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  simp [productEvaluationAlong, productEvaluation]

/-- Evaluation commutes with restricting the cover coordinate. -/
@[reassoc] theorem coverPullback_productEvaluation {Y : C} (Z : Action C H)
    (a : Z.V ⟶ Y) (F : Sheaf J (ModuleCat.{u} R)) :
    (J.overPullback (ModuleCat.{u} R) Z.V).map (coverPullback J a F) ≫
        productEvaluation J Z F = productEvaluationAlong J a F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map a (𝟙 U.unop.left)).op ≫
    F.obj.map (prod.lift U.unop.hom (𝟙 U.unop.left)).op = _
  rw [← F.obj.map_comp, ← op_comp]
  simp [productEvaluationAlong]

/-- Canonical evaluation of invariant sections after localization at any map to the cover. -/
def associatedEvaluationAlong (Y : Action C G) {Z : C} (a : Z ⟶ Y.V)
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    (J.overPullback (ModuleCat.{u} R) Z).obj (associated J Y F) ⟶
      (J.overPullback (ModuleCat.{u} R) Z).obj F.V :=
  (J.overPullback (ModuleCat.{u} R) Z).map (inclusion J Y F) ≫
    productEvaluationAlong J a F.V

@[simp] theorem associatedEvaluationAlong_id (Y : Action C G)
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    associatedEvaluationAlong J Y (𝟙 Y.V) F = associatedEvaluation J Y F := by
  simp [associatedEvaluationAlong, associatedEvaluation]

/-- Evaluation along a map is natural in the coefficient action. -/
def associatedEvaluationAlongNat (Y : Action C G) {Z : C} (a : Z ⟶ Y.V) :
    associatedFunctor (R := R) J Y ⋙ J.overPullback (ModuleCat.{u} R) Z ⟶
      Action.forget (Sheaf J (ModuleCat.{u} R)) G ⋙
        J.overPullback (ModuleCat.{u} R) Z where
  app F := associatedEvaluationAlong J Y a F
  naturality {F E} c := by
    dsimp [associatedEvaluationAlong]
    rw [← Category.assoc, ← Functor.map_comp, inclusion_natural,
      Functor.map_comp, Category.assoc, productEvaluationAlong_natural, Category.assoc]

/-- The specific cross-cover map respects canonical evaluation and the coefficient map. -/
@[reassoc] theorem crossCoverMap_evaluation
    {Y : Action C G} {Z : Action C H} (φ : H →* G)
    (a : Z ⟶ (Action.res C φ).obj Y)
    {F : Action (Sheaf J (ModuleCat.{u} R)) G}
    {E : Action (Sheaf J (ModuleCat.{u} R)) H}
    (c : (Action.res (Sheaf J (ModuleCat.{u} R)) φ).obj F ⟶ E) :
    (J.overPullback (ModuleCat.{u} R) Z.V).map (crossCoverMap J φ a c) ≫
        associatedEvaluation J Z E =
      associatedEvaluationAlong J Y a.hom F ≫
        (J.overPullback (ModuleCat.{u} R) Z.V).map c.hom := by
  dsimp only [associatedEvaluation, associatedEvaluationAlong]
  rw [← Category.assoc, ← Functor.map_comp, crossCoverMap_inclusion,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [productEvaluation_natural, ← Category.assoc
    ((J.overPullback (ModuleCat.{u} R) Z.V).map (coverPullback J a.hom F.V)),
    coverPullback_productEvaluation]

/-- Splitting of graph restrictions trivializes the associated sheaf along any map into the cover. -/
def associatedTrivializationAlongOfSplitting (Y : Action C G) {Z : C} (a : Z ⟶ Y.V)
    (hsplit : ∀ (F : Sheaf J (ModuleCat.{u} R)) (U : Over Y.V),
      Function.Bijective (fun (s : F.obj.obj (op (Y.V ⨯ U.left))) (g : G) =>
        graphRestriction J Y F U g s)) :
    (associatedFunctor J Y ⋙ J.overPullback (ModuleCat.{u} R) Z) ≅
      (Action.forget (Sheaf J (ModuleCat.{u} R)) G ⋙
        J.overPullback (ModuleCat.{u} R) Z) := by
  have hF (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
      IsIso (associatedEvaluationAlong J Y a F) := by
    have (U : (Over Z)ᵒᵖ) : IsIso ((associatedEvaluationAlong J Y a F).hom.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (associatedEvaluation_bijective J Y F ((Over.map a).obj U.unop)
          (hsplit F.V ((Over.map a).obj U.unop)))
    have := NatIso.isIso_of_isIso_app (associatedEvaluationAlong J Y a F).hom
    exact (ObjectProperty.isIso_hom_iff _).1 inferInstance
  haveI (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
      IsIso ((associatedEvaluationAlongNat (R := R) J Y a).app F) := hF F
  haveI := NatIso.isIso_of_isIso_app (associatedEvaluationAlongNat (R := R) J Y a)
  exact asIso (associatedEvaluationAlongNat (R := R) J Y a)

@[simp] theorem associatedTrivializationAlongOfSplitting_hom (Y : Action C G)
    {Z : C} (a : Z ⟶ Y.V)
    (hsplit : ∀ (F : Sheaf J (ModuleCat.{u} R)) (U : Over Y.V),
      Function.Bijective (fun (s : F.obj.obj (op (Y.V ⨯ U.left))) (g : G) =>
        graphRestriction J Y F U g s)) :
    (associatedTrivializationAlongOfSplitting J Y a hsplit).hom =
      associatedEvaluationAlongNat J Y a := rfl

end Langlands.Shimura.Coefficients
