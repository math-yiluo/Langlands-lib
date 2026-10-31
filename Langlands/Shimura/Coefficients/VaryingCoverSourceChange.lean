import Langlands.Sheaf.SourceSlice
import Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization

/-! # Source changes preserve the compatible invariant-section trivialization -/

noncomputable section

universe u uI vI v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.Sheaf

section Evaluation

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C) {R : Type u} [CommRing R]

/-- Restricting evaluation from one source slice to another evaluates at the
composite lift, under the canonical global restriction comparisons. -/
@[reassoc] theorem productEvaluationAlong_sourceChange
    {Y Z T : C} (a : T ⟶ Z) (b : Z ⟶ Y) (F : Sheaf J (ModuleCat.{u} R)) :
    (J.overMapPullback (ModuleCat.{u} R) a).map (productEvaluationAlong J b F) ≫
        (overPullbackMapIso J (ModuleCat.{u} R) a).hom.app F =
      (overPullbackMapIso J (ModuleCat.{u} R) a).hom.app ((productSheaf J Y).obj F) ≫
        productEvaluationAlong J (a ≫ b) F := by
  ext U
  simp [productEvaluationAlong, Category.assoc]

/-- The same source-change equation holds after taking invariant sections. -/
@[reassoc] theorem associatedEvaluationAlong_sourceChange
    {G : Type u} [Group G] (Y : Action C G)
    {Z T : C} (a : T ⟶ Z) (b : Z ⟶ Y.V)
    (F : Action (Sheaf J (ModuleCat.{u} R)) G) :
    (J.overMapPullback (ModuleCat.{u} R) a).map
        (associatedEvaluationAlong J Y b F) ≫
      (overPullbackMapIso J (ModuleCat.{u} R) a).hom.app F.V =
    (overPullbackMapIso J (ModuleCat.{u} R) a).hom.app (associated J Y F) ≫
      associatedEvaluationAlong J Y (a ≫ b) F := by
  dsimp only [associatedEvaluationAlong]
  rw [Functor.map_comp, Category.assoc, productEvaluationAlong_sourceChange]
  exact (overPullbackMapIso J (ModuleCat.{u} R) a).hom.naturality_assoc
    (inclusion J Y F) (productEvaluationAlong J (a ≫ b) F.V)

end Evaluation

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))

local notation "J" => Scheme.smallEtaleTopology X

@[reassoc] theorem etaleAssociatedEvaluationAlong_sourceChange
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I)
    {Z T : X.Etale} (a : T ⟶ Z) (b : Z ⟶ Y.obj.obj i) :
    ((J).overMapPullback (ModuleCat.{u} R) a).map
        (etaleAssociatedEvaluationAlong X Y M i b) ≫
      (overPullbackMapIso J (ModuleCat.{u} R) a).hom.app
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj i)) =
    (overPullbackMapIso J (ModuleCat.{u} R) a).hom.app
        ((etaleAssociatedAt X Y i).obj M) ≫
      etaleAssociatedEvaluationAlong X Y M i (a ≫ b) :=
  associatedEvaluationAlong_sourceChange J (Y.action i) a b
    (((constantSheaf J (ModuleCat.{u} R)).mapAction (D.obj i)).obj (M.action i))

/-- Restricting the associated diagram from the target cover agrees with
reindexing the diagram on the source cover. -/
def etaleAssociatedSourceChangeIso {k l : I} (f : k ⟶ l)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (sourceSliceRestriction J (ModuleCat.{u} R) Y.obj f).obj
        (etaleAssociatedSourceSystem X Y hY l M) ≅
      (sourceSliceReindex J (ModuleCat.{u} R) Y.obj f).obj
        (etaleAssociatedSourceSystem X Y hY k M) :=
  sourceSliceChangeIso J (ModuleCat.{u} R) Y.obj f
    (etaleAssociatedVaryingSystem X Y hY M)

/-- The same comparison for the original coefficient diagram made constant. -/
def etaleConstantSourceChangeIso {k l : I} (f : k ⟶ l)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (sourceSliceRestriction J (ModuleCat.{u} R) Y.obj f).obj
        (etaleConstantSourceSystem X Y l M) ≅
      (sourceSliceReindex J (ModuleCat.{u} R) Y.obj f).obj
        (etaleConstantSourceSystem X Y k M) :=
  sourceSliceChangeIso J (ModuleCat.{u} R) Y.obj f
    (M.obj ⋙ constantSheaf J (ModuleCat.{u} R))

/-- Associated source change is natural in the full equivariant coefficient
diagram, including every coefficient transition. -/
def etaleAssociatedSourceChangeFunctorIso {k l : I} (f : k ⟶ l) :
    etaleAssociatedSourceSystemFunctor (R := R) X Y hY l ⋙
        sourceSliceRestriction J (ModuleCat.{u} R) Y.obj f ≅
      etaleAssociatedSourceSystemFunctor X Y hY k ⋙
        sourceSliceReindex J (ModuleCat.{u} R) Y.obj f :=
  Functor.isoWhiskerLeft (etaleAssociatedVaryingSystemFunctor X Y hY)
    (sourceSliceChangeFunctorIso J (ModuleCat.{u} R) Y.obj f)

def etaleConstantSourceChangeFunctorIso {k l : I} (f : k ⟶ l) :
    etaleConstantSourceSystemFunctor (R := R) X Y l ⋙
        sourceSliceRestriction J (ModuleCat.{u} R) Y.obj f ≅
      etaleConstantSourceSystemFunctor X Y k ⋙
        sourceSliceReindex J (ModuleCat.{u} R) Y.obj f :=
  Functor.isoWhiskerLeft
    (EquivariantDiagram.forget ⋙
      (Functor.whiskeringRight I (ModuleCat.{u} R) (Sheaf J (ModuleCat.{u} R))).obj
        (constantSheaf J (ModuleCat.{u} R)))
    (sourceSliceChangeFunctorIso J (ModuleCat.{u} R) Y.obj f)

@[simp] theorem etaleAssociatedSourceChangeFunctorIso_app
    {k l : I} (f : k ⟶ l) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedSourceChangeFunctorIso X Y hY f).app M =
      etaleAssociatedSourceChangeIso X Y hY f M := rfl

@[simp] theorem etaleConstantSourceChangeFunctorIso_app
    {k l : I} (f : k ⟶ l) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleConstantSourceChangeFunctorIso X Y f).app M =
      etaleConstantSourceChangeIso X Y f M := rfl

/-- The constructed invariant-section trivialization commutes with changing
the source cover and its outgoing-arrow index category. -/
@[reassoc] theorem etaleAssociatedSourceTrivialization_sourceChange
    {k l : I} (f : k ⟶ l) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (sourceSliceRestriction J (ModuleCat.{u} R) Y.obj f).map
        (etaleAssociatedSourceTrivialization X Y hY l M).hom ≫
      (etaleConstantSourceChangeIso X Y f M).hom =
    (etaleAssociatedSourceChangeIso X Y hY f M).hom ≫
      (sourceSliceReindex J (ModuleCat.{u} R) Y.obj f).map
        (etaleAssociatedSourceTrivialization X Y hY k M).hom := by
  apply NatTrans.ext
  funext i
  change ((J).overMapPullback (ModuleCat.{u} R) (Y.obj.map f)).map
      (etaleAssociatedEvaluationAlong X Y M i.right (Y.obj.map i.hom)) ≫
      (overPullbackMapIso J (ModuleCat.{u} R) (Y.obj.map f)).hom.app
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj i.right)) =
    (overPullbackMapIso J (ModuleCat.{u} R) (Y.obj.map f)).hom.app
        ((etaleAssociatedAt X Y i.right).obj M) ≫
      etaleAssociatedEvaluationAlong X Y M i.right (Y.obj.map (f ≫ i.hom))
  simpa only [Functor.map_comp] using
    etaleAssociatedEvaluationAlong_sourceChange X Y M i.right
      (Y.obj.map f) (Y.obj.map i.hom)

/-- The compatibility square is an equality of natural transformations on
the whole category of equivariant coefficient diagrams. -/
@[reassoc] theorem etaleAssociatedSourceTrivializationFunctor_sourceChange
    {k l : I} (f : k ⟶ l) :
    Functor.whiskerRight (etaleAssociatedSourceTrivializationFunctor (R := R) X Y hY l).hom
        (sourceSliceRestriction J (ModuleCat.{u} R) Y.obj f) ≫
      (etaleConstantSourceChangeFunctorIso X Y f).hom =
    (etaleAssociatedSourceChangeFunctorIso X Y hY f).hom ≫
      Functor.whiskerRight (etaleAssociatedSourceTrivializationFunctor X Y hY k).hom
        (sourceSliceReindex J (ModuleCat.{u} R) Y.obj f) := by
  apply NatTrans.ext
  funext M
  exact etaleAssociatedSourceTrivialization_sourceChange X Y hY f M

end Langlands.Shimura.Coefficients
