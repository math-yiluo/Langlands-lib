import Langlands.Shimura.Coefficients.VaryingCoverInverse

/-! # Contravariant cover change of whole varying-torsor systems -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable {Y Z W : EquivariantDiagram D X.Etale}

/-- Pure cover change is normalized by the actual invariant inclusion. -/
@[reassoc] theorem etaleCrossCoverMap_identity_inclusion
    {G H : Type u} [Group G] [Group H]
    {A : Action X.Etale G} {B : Action X.Etale H}
    (φ : H →* G) (a : B ⟶ (Action.res X.Etale φ).obj A)
    (M : Action (ModuleCat.{u} R) G) :
    etaleCrossCoverMap X φ a (𝟙 ((Action.res (ModuleCat.{u} R) φ).obj M)) ≫
        etaleAssociatedInclusion X B ((Action.res (ModuleCat.{u} R) φ).obj M) =
      etaleAssociatedInclusion X A M ≫
        coverPullback X.smallEtaleTopology a.hom
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V) := by
  change crossCoverMap X.smallEtaleTopology φ a _ ≫ inclusion _ _ _ = _
  rw [crossCoverMap_inclusion]
  simp
  rfl

/-- A cover-diagram map induces a contravariant associated map at each vertex. -/
def etaleAssociatedAtCoverChange (a : Y ⟶ Z) (i : I) :
    etaleAssociatedAt (R := R) X Z i ⟶ etaleAssociatedAt X Y i :=
  Functor.whiskerLeft (EquivariantDiagram.evaluation i)
    (etaleAssociatedCoverChange X (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map a))

@[simp] theorem etaleAssociatedAtCoverChange_app (a : Y ⟶ Z) (i : I)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedAtCoverChange X R a i).app M =
      etaleCrossCoverMap X (MonoidHom.id (D.obj i))
        ((EquivariantDiagram.evaluation i).map a) (𝟙 (M.action i)) := rfl

@[simp] theorem etaleAssociatedAtCoverChange_id (i : I) :
    etaleAssociatedAtCoverChange X R (𝟙 Y) i = 𝟙 (etaleAssociatedAt X Y i) := by
  apply NatTrans.ext
  funext M
  apply (cancel_mono (etaleAssociatedInclusion X (Y.action i) (M.action i))).1
  simp only [etaleAssociatedAtCoverChange_app, NatTrans.id_app, Category.id_comp]
  erw [etaleCrossCoverMap_identity_inclusion X (R := R)
    (A := Y.action i) (B := Y.action i) (MonoidHom.id (D.obj i))
    ((EquivariantDiagram.evaluation i).map (𝟙 Y)) (M.action i)]
  change etaleAssociatedInclusion X (Y.action i) (M.action i) ≫
    coverPullback X.smallEtaleTopology (𝟙 (Y.obj.obj i))
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj i)) = _
  erw [coverPullback_id, Category.comp_id]

/-- Vertex cover change reverses composition of cover-diagram maps. -/
@[reassoc] theorem etaleAssociatedAtCoverChange_comp
    (a : Y ⟶ Z) (b : Z ⟶ W) (i : I) :
    etaleAssociatedAtCoverChange X R b i ≫ etaleAssociatedAtCoverChange X R a i =
      etaleAssociatedAtCoverChange X R (a ≫ b) i := by
  apply NatTrans.ext
  funext M
  apply (cancel_mono (etaleAssociatedInclusion X (Y.action i) (M.action i))).1
  simp only [NatTrans.comp_app, Category.assoc, etaleAssociatedAtCoverChange_app]
  erw [etaleCrossCoverMap_identity_inclusion X (R := R)
      (A := Z.action i) (B := Y.action i) (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map a) (M.action i),
    etaleCrossCoverMap_identity_inclusion_assoc X (R := R)
      (A := W.action i) (B := Z.action i) (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map b) (M.action i),
    etaleCrossCoverMap_identity_inclusion X (R := R)
      (A := W.action i) (B := Y.action i) (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map (a ≫ b)) (M.action i)]
  change etaleAssociatedInclusion X (W.action i) (M.action i) ≫
      coverPullback X.smallEtaleTopology (b.hom.app i)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj i)) ≫
      coverPullback X.smallEtaleTopology (a.hom.app i)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj i)) =
    etaleAssociatedInclusion X (W.action i) (M.action i) ≫
      coverPullback X.smallEtaleTopology (a.hom.app i ≫ b.hom.app i)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj i))
  rw [coverPullback_comp]

/-- Cover change commutes with coefficient reduction on the source vertex. -/
@[reassoc] theorem etaleAssociatedReduction_coverChange (a : Y ⟶ Z)
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedAtCoverChange X R a i).app M ≫
        (etaleAssociatedReduction X Y b).app M =
      (etaleAssociatedReduction X Z b).app M ≫
        etaleCrossCoverMap X (MonoidHom.id (D.obj i))
          ((EquivariantDiagram.evaluation i).map a)
          (𝟙 ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j))) := by
  apply (cancel_mono (etaleAssociatedInclusion X (Y.action i)
    ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j)))).1
  simp only [etaleAssociatedAtCoverChange_app, Category.assoc,
    etaleAssociatedReduction_inclusion]
  erw [etaleCrossCoverMap_identity_inclusion_assoc X (R := R)
      (A := Z.action i) (B := Y.action i) (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map a) (M.action i),
    etaleCrossCoverMap_identity_inclusion X (R := R)
      (A := Z.action i) (B := Y.action i) (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map a)
      ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j))]
  rw [etaleAssociatedReduction_inclusion_assoc]
  exact congrArg (fun k => etaleAssociatedInclusion X (Z.action i) (M.action i) ≫ k)
    (coverPullback_natural X.smallEtaleTopology (a.hom.app i)
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (M.obj.map b)))

/-- The cover-comparison legs commute by naturality of the cover diagram map. -/
@[reassoc] theorem etaleAssociatedComparison_coverChange (a : Y ⟶ Z)
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedAtCoverChange X R a j).app M ≫
        (etaleAssociatedComparison X Y b).app M =
      (etaleAssociatedComparison X Z b).app M ≫
        etaleCrossCoverMap X (MonoidHom.id (D.obj i))
          ((EquivariantDiagram.evaluation i).map a)
          (𝟙 ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j))) := by
  apply (cancel_mono (etaleAssociatedInclusion X (Y.action i)
    ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j)))).1
  simp only [etaleAssociatedAtCoverChange_app, Category.assoc,
    etaleAssociatedComparison_inclusion]
  erw [etaleCrossCoverMap_identity_inclusion_assoc X (R := R)
      (A := Z.action j) (B := Y.action j) (MonoidHom.id (D.obj j))
      ((EquivariantDiagram.evaluation j).map a) (M.action j),
    etaleCrossCoverMap_identity_inclusion X (R := R)
      (A := Z.action i) (B := Y.action i) (MonoidHom.id (D.obj i))
      ((EquivariantDiagram.evaluation i).map a)
      ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j))]
  rw [etaleAssociatedComparison_inclusion_assoc]
  change etaleAssociatedInclusion X (Z.action j) (M.action j) ≫
      coverPullback X.smallEtaleTopology (a.hom.app j)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj j)) ≫
      coverPullback X.smallEtaleTopology (Y.obj.map b)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj j)) =
    etaleAssociatedInclusion X (Z.action j) (M.action j) ≫
      coverPullback X.smallEtaleTopology (Z.obj.map b)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj j)) ≫
      coverPullback X.smallEtaleTopology (a.hom.app i)
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.obj.obj j))
  rw [← coverPullback_comp, ← coverPullback_comp]
  exact congrArg (fun k => etaleAssociatedInclusion X (Z.action j) (M.action j) ≫
    coverPullback X.smallEtaleTopology k
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (M.action j).V))
    (a.hom.naturality b)

/-- Contravariant cover change respects the actual inverse-cover transitions. -/
@[reassoc] theorem etaleAssociatedTransition_coverChange
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i))
    (a : Y ⟶ Z) {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedTransition X Z hZ b).app M ≫
        (etaleAssociatedAtCoverChange X R a j).app M =
      (etaleAssociatedAtCoverChange X R a i).app M ≫
        (etaleAssociatedTransition X Y hY b).app M := by
  let := etaleAssociatedComparison_app_isIso X Y hY b M
  apply (cancel_mono ((etaleAssociatedComparison X Y b).app M)).1
  rw [Category.assoc, etaleAssociatedComparison_coverChange,
    ← Category.assoc, etaleAssociatedTransition_comparison,
    Category.assoc, etaleAssociatedTransition_comparison,
    etaleAssociatedReduction_coverChange]

/-- Whole associated-sheaf systems vary contravariantly with their cover diagram. -/
def etaleAssociatedVaryingSystemCoverChange
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i)) (a : Y ⟶ Z) :
    etaleAssociatedVaryingSystemFunctor (R := R) X Z hZ ⟶
      etaleAssociatedVaryingSystemFunctor X Y hY where
  app M :=
    { app i := (etaleAssociatedAtCoverChange X R a i).app M
      naturality {_i _j} b := etaleAssociatedTransition_coverChange X R hY hZ a b M }
  naturality {_M _N} c := by
    apply NatTrans.ext
    funext i
    exact (etaleAssociatedAtCoverChange X R a i).naturality c

@[simp] theorem etaleAssociatedVaryingSystemCoverChange_app
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i)) (a : Y ⟶ Z)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingSystemCoverChange X R hY hZ a).app M).app i =
      etaleCrossCoverMap X (MonoidHom.id (D.obj i))
        ((EquivariantDiagram.evaluation i).map a) (𝟙 (M.action i)) := rfl

@[simp] theorem etaleAssociatedVaryingSystemCoverChange_id
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) :
    etaleAssociatedVaryingSystemCoverChange X R hY hY (𝟙 Y) =
      𝟙 (etaleAssociatedVaryingSystemFunctor X Y hY) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext i
  exact congrArg (fun k => k.app M) (etaleAssociatedAtCoverChange_id X R (Y := Y) i)

/-- Whole-system cover change is contravariantly compatible with composition. -/
@[reassoc] theorem etaleAssociatedVaryingSystemCoverChange_comp
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i))
    (hW : ∀ i, IsFiniteGeometricTorsor X (W.action i)) (a : Y ⟶ Z) (b : Z ⟶ W) :
    etaleAssociatedVaryingSystemCoverChange X R hZ hW b ≫
        etaleAssociatedVaryingSystemCoverChange X R hY hZ a =
      etaleAssociatedVaryingSystemCoverChange X R hY hW (a ≫ b) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext i
  exact congrArg (fun k => k.app M) (etaleAssociatedAtCoverChange_comp X R a b i)

/-- An isomorphism of cover diagrams induces the opposite isomorphism of systems. -/
def etaleAssociatedVaryingSystemCoverIso
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i)) (e : Y ≅ Z) :
    etaleAssociatedVaryingSystemFunctor (R := R) X Z hZ ≅
      etaleAssociatedVaryingSystemFunctor X Y hY where
  hom := etaleAssociatedVaryingSystemCoverChange X R hY hZ e.hom
  inv := etaleAssociatedVaryingSystemCoverChange X R hZ hY e.inv
  hom_inv_id := by
    rw [etaleAssociatedVaryingSystemCoverChange_comp, e.inv_hom_id,
      etaleAssociatedVaryingSystemCoverChange_id]
  inv_hom_id := by
    rw [etaleAssociatedVaryingSystemCoverChange_comp, e.hom_inv_id,
      etaleAssociatedVaryingSystemCoverChange_id]

end Langlands.Shimura.Coefficients
