import Langlands.Shimura.Coefficients.VaryingCover
import Langlands.Shimura.Coefficients.EtaleCoverComparisonProof

/-! # Associated sheaf diagrams on varying finite geometric torsors -/

noncomputable section

universe u uI vI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]

/-- Include an associated etale coefficient sheaf in sections over its cover. -/
def etaleAssociatedInclusion {G : Type u} [Group G]
    (Y : Action X.Etale G) (M : Action (ModuleCat.{u} R) G) :
    (etaleAssociatedFunctor X Y).obj M ⟶
      (productSheaf (Scheme.smallEtaleTopology X) Y.V).obj
        ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).obj M.V) :=
  inclusion (Scheme.smallEtaleTopology X) Y
    (((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).mapAction G).obj M)

instance etaleAssociatedInclusion_mono {G : Type u} [Group G]
    (Y : Action X.Etale G) (M : Action (ModuleCat.{u} R) G) :
    Mono (etaleAssociatedInclusion X Y M) :=
  inclusion_mono _ _ _

@[reassoc] theorem etaleAssociatedInclusion_natural {G : Type u} [Group G]
    (Y : Action X.Etale G) {M N : Action (ModuleCat.{u} R) G} (c : M ⟶ N) :
    (etaleAssociatedFunctor X Y).map c ≫ etaleAssociatedInclusion X Y N =
      etaleAssociatedInclusion X Y M ≫
        (productSheaf (Scheme.smallEtaleTopology X) Y.V).map
          ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).map c.hom) :=
  inclusion_natural (Scheme.smallEtaleTopology X) Y
    (((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).mapAction G).map c)

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)

/-- Finite geometric torsors make the exact comparison cospan leg invertible. -/
theorem etaleAssociatedComparison_app_isIso
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    {i j : I} (f : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    IsIso ((etaleAssociatedComparison X Y f).app M) :=
  etaleAssociatedCoverComparison X (D.obj j) (D.obj i)
    (Y.action j) (Y.action i) (hY j) (hY i)
    (D.map f).hom (Y.transition f) R (M.action j)

/-- The cover comparison is a natural isomorphism in the whole coefficient diagram. -/
def etaleAssociatedComparisonIso
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) {i j : I} (f : i ⟶ j) :
    etaleAssociatedAt (R := R) X Y j ≅ etaleAssociatedTransitionTarget X Y f :=
  NatIso.ofComponents (fun M => by
    letI := etaleAssociatedComparison_app_isIso X Y hY f M
    exact asIso ((etaleAssociatedComparison X Y f).app M))
    (fun c => (etaleAssociatedComparison X Y f).naturality c)

@[simp] theorem etaleAssociatedComparisonIso_hom
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) {i j : I} (f : i ⟶ j) :
    (etaleAssociatedComparisonIso (R := R) X Y hY f).hom =
      etaleAssociatedComparison X Y f := rfl

/-- Coefficient reduction followed by the inverse of the proved cover comparison. -/
def etaleAssociatedTransition
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) {i j : I} (f : i ⟶ j) :
    etaleAssociatedAt (R := R) X Y i ⟶ etaleAssociatedAt X Y j :=
  etaleAssociatedReduction X Y f ≫ (etaleAssociatedComparisonIso X Y hY f).inv

@[reassoc] theorem etaleAssociatedTransition_comparison
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) {i j : I} (f : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedTransition X Y hY f).app M ≫
        (etaleAssociatedComparison X Y f).app M =
      (etaleAssociatedReduction X Y f).app M := by
  change ((etaleAssociatedReduction X Y f).app M ≫
      (etaleAssociatedComparisonIso X Y hY f).inv.app M) ≫
      (etaleAssociatedComparisonIso X Y hY f).hom.app M = _
  rw [Category.assoc]
  rw [show (etaleAssociatedComparisonIso X Y hY f).inv.app M ≫
      (etaleAssociatedComparisonIso X Y hY f).hom.app M = 𝟙 _ from
      ((etaleAssociatedComparisonIso X Y hY f).app M).inv_hom_id, Category.comp_id]

@[reassoc] theorem etaleAssociatedComparison_inclusion {i j : I} (f : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedComparison X Y f).app M ≫
        etaleAssociatedInclusion X (Y.action i)
          ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)) =
      etaleAssociatedInclusion X (Y.action j) (M.action j) ≫
        coverPullback (Scheme.smallEtaleTopology X) (Y.obj.map f)
          ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).obj
            (M.obj.obj j)) := by
  change crossCoverMap (Scheme.smallEtaleTopology X) (D.map f).hom
      (Y.transition f) _ ≫ inclusion _ _ _ = _
  rw [crossCoverMap_inclusion]
  simp
  rfl

@[reassoc] theorem etaleAssociatedReduction_inclusion {i j : I} (f : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedReduction X Y f).app M ≫
        etaleAssociatedInclusion X (Y.action i)
          ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)) =
      etaleAssociatedInclusion X (Y.action i) (M.action i) ≫
        (productSheaf (Scheme.smallEtaleTopology X) (Y.obj.obj i)).map
          ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).map
            (M.obj.map f)) :=
  etaleAssociatedInclusion_natural X (Y.action i) (M.transition f)

/-- The transition is characterized on actual sections by coefficient reduction
and pullback along the cover map. -/
@[reassoc] theorem etaleAssociatedTransition_inclusion
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) {i j : I} (f : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedTransition X Y hY f).app M ≫
        etaleAssociatedInclusion X (Y.action j) (M.action j) ≫
        coverPullback (Scheme.smallEtaleTopology X) (Y.obj.map f)
          ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).obj
            (M.obj.obj j)) =
      etaleAssociatedInclusion X (Y.action i) (M.action i) ≫
        (productSheaf (Scheme.smallEtaleTopology X) (Y.obj.obj i)).map
          ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).map
            (M.obj.map f)) := by
  rw [← etaleAssociatedComparison_inclusion, ← Category.assoc,
    etaleAssociatedTransition_comparison, etaleAssociatedReduction_inclusion]

/-- Equality after cover pullback detects maps into the target associated sheaf. -/
theorem etaleAssociatedTransition_hom_ext
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) {i j : I} (f : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R))
    {T : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)}
    {a b : T ⟶ (etaleAssociatedAt X Y j).obj M}
    (h : a ≫ etaleAssociatedInclusion X (Y.action j) (M.action j) ≫
          coverPullback (Scheme.smallEtaleTopology X) (Y.obj.map f)
            ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).obj
              (M.obj.obj j)) =
        b ≫ etaleAssociatedInclusion X (Y.action j) (M.action j) ≫
          coverPullback (Scheme.smallEtaleTopology X) (Y.obj.map f)
            ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).obj
              (M.obj.obj j))) : a = b := by
  let := etaleAssociatedComparison_app_isIso X Y hY f M
  apply (cancel_mono ((etaleAssociatedComparison X Y f).app M)).1
  apply (cancel_mono (etaleAssociatedInclusion X (Y.action i)
    ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)))).1
  simpa only [Category.assoc, etaleAssociatedComparison_inclusion] using h

@[simp] theorem etaleAssociatedTransition_id
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    (etaleAssociatedTransition X Y hY (𝟙 i)).app M =
      𝟙 ((etaleAssociatedAt X Y i).obj M) := by
  apply (cancel_mono (etaleAssociatedInclusion X (Y.action i) (M.action i))).1
  have h := etaleAssociatedTransition_inclusion X Y hY (𝟙 i) M
  rw [Y.obj.map_id, M.obj.map_id] at h
  dsimp only [EquivariantDiagram.action] at h ⊢
  erw [coverPullback_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at h
  simpa only [Category.id_comp] using h

/-- Varying-cover transitions satisfy composition in the index category. -/
theorem etaleAssociatedTransition_comp
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (M : EquivariantDiagram D (ModuleCat.{u} R))
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) :
    (etaleAssociatedTransition X Y hY f).app M ≫
        (etaleAssociatedTransition X Y hY g).app M =
      (etaleAssociatedTransition X Y hY (f ≫ g)).app M := by
  apply etaleAssociatedTransition_hom_ext X Y hY (f ≫ g) M
  rw [etaleAssociatedTransition_inclusion X Y hY (f ≫ g) M,
    Y.obj.map_comp, coverPullback_comp]
  simp only [Category.assoc]
  rw [etaleAssociatedTransition_inclusion_assoc X Y hY g M,
    ← coverPullback_natural]
  erw [etaleAssociatedTransition_inclusion_assoc X Y hY f M]
  simp only [M.obj.map_comp, CategoryTheory.Functor.map_comp]

/-- The actual associated-sheaf diagram on varying finite geometric torsors. -/
def etaleAssociatedVaryingSystem
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    I ⥤ Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R) where
  obj i := (etaleAssociatedAt X Y i).obj M
  map f := (etaleAssociatedTransition X Y hY f).app M
  map_id i := etaleAssociatedTransition_id X Y hY M i
  map_comp f g := (etaleAssociatedTransition_comp X Y hY M f g).symm

/-- Varying-cover associated-sheaf diagrams are functorial in coefficient diagrams. -/
def etaleAssociatedVaryingSystemFunctor
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (I ⥤ Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)) where
  obj M := etaleAssociatedVaryingSystem X Y hY M
  map c :=
    { app i := (etaleAssociatedAt X Y i).map c
      naturality {_i _j} f := ((etaleAssociatedTransition X Y hY f).naturality c).symm }
  map_id M := NatTrans.ext (funext fun i => (etaleAssociatedAt X Y i).map_id M)
  map_comp c d := NatTrans.ext (funext fun i => (etaleAssociatedAt X Y i).map_comp c d)

@[simp] theorem etaleAssociatedVaryingSystem_obj
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    (etaleAssociatedVaryingSystem X Y hY M).obj i =
      (etaleAssociatedFunctor X (Y.action i)).obj (M.action i) := rfl

@[simp] theorem etaleAssociatedVaryingSystem_map
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    (M : EquivariantDiagram D (ModuleCat.{u} R)) {i j : I} (f : i ⟶ j) :
    (etaleAssociatedVaryingSystem X Y hY M).map f =
      (etaleAssociatedReduction X Y f).app M ≫
        (etaleAssociatedComparisonIso X Y hY f).inv.app M := rfl

@[simp] theorem etaleAssociatedVaryingSystemFunctor_map_app
    (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
    {M N : EquivariantDiagram D (ModuleCat.{u} R)} (c : M ⟶ N) (i : I) :
    ((etaleAssociatedVaryingSystemFunctor X Y hY).map c).app i =
      (etaleAssociatedFunctor X (Y.action i)).map
        ((EquivariantDiagram.evaluation i).map c) := rfl

end Langlands.Shimura.Coefficients
