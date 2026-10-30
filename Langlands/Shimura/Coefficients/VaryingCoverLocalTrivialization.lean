import Langlands.Shimura.Coefficients.VaryingCoverInverse
import Langlands.Shimura.Coefficients.CrossCoverEvaluation
import Langlands.Shimura.Coefficients.TorsorSectionSplittingProof

/-! # Compatible trivialization of a varying-cover diagram on a source cover -/

noncomputable section

universe u uI vI v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Evaluation

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C) {R : Type u} [CommRing R]

/-- Restricting the cover coordinate and evaluating along a lift is evaluation
along the composite lift. -/
@[reassoc] theorem coverPullback_productEvaluationAlong
    {Y Z T : C} (a : T ⟶ Z) (b : Z ⟶ Y) (F : Sheaf J (ModuleCat.{u} R)) :
    (J.overPullback (ModuleCat.{u} R) T).map (coverPullback J b F) ≫
        productEvaluationAlong J a F =
      productEvaluationAlong J (a ≫ b) F := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map b (𝟙 U.unop.left)).op ≫
      F.obj.map (prod.lift (U.unop.hom ≫ a) (𝟙 U.unop.left)).op = _
  rw [← F.obj.map_comp, ← op_comp]
  simp [productEvaluationAlong, Category.assoc]

end Evaluation

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))

local notation "J" => Scheme.smallEtaleTopology X

/-- Invariant-section evaluation for a coefficient diagram along a map into
one of its covers. -/
def etaleAssociatedEvaluationAlong
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I)
    {Z : X.Etale} (a : Z ⟶ Y.obj.obj i) :
    ((J).overPullback (ModuleCat.{u} R) Z).obj
        ((etaleAssociatedAt X Y i).obj M) ⟶
      ((J).overPullback (ModuleCat.{u} R) Z).obj
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj i)) :=
  associatedEvaluationAlong J (Y.action i) a
    (((constantSheaf J (ModuleCat.{u} R)).mapAction (D.obj i)).obj (M.action i))

/-- Evaluation also respects maps of the complete coefficient diagrams. -/
@[reassoc] theorem etaleAssociatedEvaluationAlong_natural
    {M N : EquivariantDiagram D (ModuleCat.{u} R)} (c : M ⟶ N)
    (i : I) {Z : X.Etale} (a : Z ⟶ Y.obj.obj i) :
    ((J).overPullback (ModuleCat.{u} R) Z).map ((etaleAssociatedAt X Y i).map c) ≫
        etaleAssociatedEvaluationAlong X Y N i a =
      etaleAssociatedEvaluationAlong X Y M i a ≫
        ((J).overPullback (ModuleCat.{u} R) Z).map
          ((constantSheaf J (ModuleCat.{u} R)).map (c.hom.app i)) :=
  (associatedEvaluationAlongNat J (Y.action i) a).naturality
    (((constantSheaf J (ModuleCat.{u} R)).mapAction (D.obj i)).map
      ((EquivariantDiagram.evaluation i).map c))

/-- The actual varying-cover transition commutes with evaluation along every
map into its source cover and the original coefficient transition. -/
@[reassoc] theorem etaleAssociatedTransition_evaluationAlong
    (M : EquivariantDiagram D (ModuleCat.{u} R))
    {i j : I} (f : i ⟶ j) {Z : X.Etale} (a : Z ⟶ Y.obj.obj i) :
    ((J).overPullback (ModuleCat.{u} R) Z).map
        ((etaleAssociatedTransition X Y hY f).app M) ≫
      etaleAssociatedEvaluationAlong X Y M j (a ≫ Y.obj.map f) =
    etaleAssociatedEvaluationAlong X Y M i a ≫
      ((J).overPullback (ModuleCat.{u} R) Z).map
        ((constantSheaf J (ModuleCat.{u} R)).map (M.obj.map f)) := by
  have h := congrArg
    (fun t => ((J).overPullback (ModuleCat.{u} R) Z).map t ≫
      productEvaluationAlong J a
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)))
    (etaleAssociatedTransition_inclusion X Y hY f M)
  simpa only [Functor.map_comp, Category.assoc,
    coverPullback_productEvaluationAlong, productEvaluationAlong_natural,
    etaleAssociatedEvaluationAlong, associatedEvaluationAlong,
    etaleAssociatedInclusion, Functor.mapAction, EquivariantDiagram.action] using h

/-- All terms reachable from a source index, localized on that source cover. -/
def etaleAssociatedSourceSystem (k : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    Under k ⥤ Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R) :=
  Under.forget k ⋙ etaleAssociatedVaryingSystem X Y hY M ⋙
    (J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)

/-- The original underlying coefficient diagram on the same slice site. -/
def etaleConstantSourceSystem (k : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    Under k ⥤ Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R) :=
  Under.forget k ⋙ M.obj ⋙ constantSheaf J (ModuleCat.{u} R) ⋙
    (J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)

/-- Evaluation is a morphism of the entire source-localized diagrams. -/
def etaleAssociatedSourceEvaluation (k : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    etaleAssociatedSourceSystem X Y hY k M ⟶ etaleConstantSourceSystem X Y k M where
  app i := etaleAssociatedEvaluationAlong X Y M i.right (Y.obj.map i.hom)
  naturality {i j} f := by
    change ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)).map
        ((etaleAssociatedTransition X Y hY f.right).app M) ≫
        etaleAssociatedEvaluationAlong X Y M j.right (Y.obj.map j.hom) =
      etaleAssociatedEvaluationAlong X Y M i.right (Y.obj.map i.hom) ≫
        ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj k)).map
          ((constantSheaf J (ModuleCat.{u} R)).map (M.obj.map f.right))
    have h := etaleAssociatedTransition_evaluationAlong X Y hY M f.right
      (Y.obj.map i.hom)
    simpa only [← Y.obj.map_comp, Under.w] using h

/-- Geometric graph splitting makes every evaluation component invertible. -/
def etaleAssociatedTrivializationAlong
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I)
    {Z : X.Etale} (a : Z ⟶ Y.obj.obj i) :
    ((J).overPullback (ModuleCat.{u} R) Z).obj
        ((etaleAssociatedAt X Y i).obj M) ≅
      ((J).overPullback (ModuleCat.{u} R) Z).obj
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj i)) :=
  (associatedTrivializationAlongOfSplitting J (Y.action i) a
    (etaleTorsorSectionSplitting X _ (Y.action i) (hY i) R)).app
      (((constantSheaf J (ModuleCat.{u} R)).mapAction (D.obj i)).obj (M.action i))

@[simp] theorem etaleAssociatedTrivializationAlong_hom
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I)
    {Z : X.Etale} (a : Z ⟶ Y.obj.obj i) :
    (etaleAssociatedTrivializationAlong X Y hY M i a).hom =
      etaleAssociatedEvaluationAlong X Y M i a := rfl

/-- The whole reachable coefficient diagram is canonically trivialized on
the fixed source cover, with its original coefficient transitions. -/
def etaleAssociatedSourceTrivialization (k : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    etaleAssociatedSourceSystem X Y hY k M ≅ etaleConstantSourceSystem X Y k M :=
  NatIso.ofComponents
    (fun i => etaleAssociatedTrivializationAlong X Y hY M i.right (Y.obj.map i.hom))
    (fun f => (etaleAssociatedSourceEvaluation X Y hY k M).naturality f)

@[simp] theorem etaleAssociatedSourceTrivialization_hom (k : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedSourceTrivialization X Y hY k M).hom =
      etaleAssociatedSourceEvaluation X Y hY k M := rfl

/-- Source localization is functorial in the whole coefficient diagram. -/
def etaleAssociatedSourceSystemFunctor (k : I) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (Under k ⥤ Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R)) :=
  etaleAssociatedVaryingSystemFunctor X Y hY ⋙
    (Functor.whiskeringLeft (Under k) I (Sheaf J (ModuleCat.{u} R))).obj
      (Under.forget k) ⋙
    (Functor.whiskeringRight (Under k) (Sheaf J (ModuleCat.{u} R))
      (Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R))).obj
        ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj k))

/-- Forgetting the actions and then forming localized constant sheaves is
functorial in the same coefficient diagrams. -/
def etaleConstantSourceSystemFunctor (k : I) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (Under k ⥤ Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R)) :=
  EquivariantDiagram.forget ⋙
    (Functor.whiskeringLeft (Under k) I (ModuleCat.{u} R)).obj (Under.forget k) ⋙
    (Functor.whiskeringRight (Under k) (ModuleCat.{u} R)
      (Sheaf J (ModuleCat.{u} R))).obj (constantSheaf J (ModuleCat.{u} R)) ⋙
    (Functor.whiskeringRight (Under k) (Sheaf J (ModuleCat.{u} R))
      (Sheaf ((J).over (Y.obj.obj k)) (ModuleCat.{u} R))).obj
        ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj k))

/-- The source-localized diagram isomorphism is natural in all coefficient
diagrams and their equivariant morphisms. -/
def etaleAssociatedSourceTrivializationFunctor (k : I) :
    etaleAssociatedSourceSystemFunctor (R := R) X Y hY k ≅
      etaleConstantSourceSystemFunctor X Y k :=
  NatIso.ofComponents (fun M => etaleAssociatedSourceTrivialization X Y hY k M)
    (fun c => by
      apply NatTrans.ext
      funext i
      exact etaleAssociatedEvaluationAlong_natural X Y c i.right (Y.obj.map i.hom))

@[simp] theorem etaleAssociatedSourceTrivializationFunctor_app (k : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedSourceTrivializationFunctor X Y hY k).app M =
      etaleAssociatedSourceTrivialization X Y hY k M := rfl

end Langlands.Shimura.Coefficients
