import Langlands.GroupScheme.RelativeUnipotent.FreeVectorBundle
import Langlands.GroupScheme.RelativeLevi.FiniteFaceCoverGeometry
import Langlands.GroupScheme.RelativeUnipotent.DisjointBundlePoints

/-! # The actual vector-bundle module of the assembled face layers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

/-- Transport fixed-module point charts along an actual group isomorphism. -/
def groupIsoPoints {S : Scheme.{u}} {V W : GroupScheme S} (e : V ≅ W) (M : S.Modules)
    (c : ∀ T : Over S, (T ⟶ W.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)))
    (T : Over S) :
    (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :=
  vectorBundlePointsOfIso e.symm M c T

/-- Isomorphism transport retains canonical naturality without expanding the
construction of either group. -/
lemma groupIsoPoints_natural {S : Scheme.{u}} {V W : GroupScheme S}
    (e : V ≅ W) (M : S.Modules)
    (c : ∀ T : Over S, (T ⟶ W.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)))
    (hc : ∀ (T T' : Over S) (b : T' ⟶ T) (x : T ⟶ W.X),
      (c T' (b ≫ x)).toAdd = sectionPullback M b (c T x).toAdd)
    (T T' : Over S) (b : T' ⟶ T) (x : T ⟶ V.X) :
    (groupIsoPoints e M c T' (b ≫ x)).toAdd =
      sectionPullback M b (groupIsoPoints e M c T x).toAdd := by
  simpa only [groupIsoPoints, vectorBundlePointsOfIso_apply, Iso.symm_inv, Category.assoc] using hc T T' b (x ≫ e.hom.hom.hom)

/-- Relative section pullback is natural in the actual coefficient module. -/
lemma sectionPullback_moduleHom {S : Scheme.{u}} {A B : S.Modules} (f : A ⟶ B)
    {T W : Over S} (b : W ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj A)) :
    ((Scheme.Modules.pullback W.hom).map f).app ⊤ (sectionPullback A b s) =
      sectionPullback B b (((Scheme.Modules.pullback T.hom).map f).app ⊤ s) := by
  let comparisonNat := (Scheme.Modules.pullbackComp b.left T.hom).hom ≫
    (Scheme.Modules.pullbackCongr (Over.w b)).hom
  change ((Scheme.Modules.pullback W.hom).map f).app ⊤
      ((comparisonNat.app A).app ⊤ (pullbackSection b.left _ s)) =
    (comparisonNat.app B).app ⊤ (pullbackSection b.left _
      (((Scheme.Modules.pullback T.hom).map f).app ⊤ s))
  rw [pullbackSection_naturality]
  change (comparisonNat.app A ≫ (Scheme.Modules.pullback W.hom).map f).app ⊤
      (pullbackSection b.left _ s) =
    ((Scheme.Modules.pullback b.left).map ((Scheme.Modules.pullback T.hom).map f) ≫
      comparisonNat.app B).app ⊤ (pullbackSection b.left _ s)
  exact congrArg (fun g => g.app ⊤ (pullbackSection b.left _ s)) (comparisonNat.naturality f).symm

/-- Transport actual point coordinates through an actual module-sheaf isomorphism. -/
def moduleIsoPoints {S : Scheme.{u}} {V : GroupScheme S} {A B : S.Modules}
    (e : A ≅ B)
    (c : ∀ T : Over S, (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj B)))
    (T : Over S) :
    (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj A)) :=
  (c T).trans (AddEquiv.toMultiplicative
    (LinearModuleCharts.sectionIsoEquiv ((Scheme.Modules.pullback T.hom).mapIso e).symm))

/-- The transported chart recovers the original section under the prescribed module map. -/
lemma moduleIsoPoints_map {S : Scheme.{u}} {V : GroupScheme S} {A B : S.Modules}
    (e : A ≅ B)
    (c : ∀ T : Over S, (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj B)))
    (T : Over S) (x : T ⟶ V.X) :
    ((Scheme.Modules.pullback T.hom).map e.hom).app ⊤
        (moduleIsoPoints e c T x).toAdd = (c T x).toAdd := by
  change ((Scheme.Modules.pullback T.hom).map e.hom).app ⊤
    (((Scheme.Modules.pullback T.hom).map e.inv).app ⊤ (c T x).toAdd) = _
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
    Scheme.Modules.Hom.id_app]
  rfl

/-- Actual module isomorphisms preserve the canonical naturality of point charts. -/
lemma moduleIsoPoints_natural {S : Scheme.{u}} {V : GroupScheme S} {A B : S.Modules}
    (e : A ≅ B)
    (c : ∀ T : Over S, (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj B)))
    (hc : ∀ (T W : Over S) (b : W ⟶ T) (x : T ⟶ V.X),
      (c W (b ≫ x)).toAdd = sectionPullback B b (c T x).toAdd)
    (T W : Over S) (b : W ⟶ T) (x : T ⟶ V.X) :
    (moduleIsoPoints e c W (b ≫ x)).toAdd =
      sectionPullback A b (moduleIsoPoints e c T x).toAdd := by
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback W.hom).mapIso e).hom.app ⊤)).injective
  change ((Scheme.Modules.pullback W.hom).map e.hom).app ⊤
      (moduleIsoPoints e c W (b ≫ x)).toAdd =
    ((Scheme.Modules.pullback W.hom).map e.hom).app ⊤
      (sectionPullback A b (moduleIsoPoints e c T x).toAdd)
  rw [moduleIsoPoints_map, sectionPullback_moduleHom, moduleIsoPoints_map]
  exact hc T W b x

end Langlands.GroupScheme.RelativeUnipotent

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)

local instance bundleAmbientAffine {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

local instance bundleAmbientSourceAffine (a : D.Index) :
    IsAffine ((baseChange (D.charts a.down).2.projection).obj G).X.left :=
  isAffine_of_isAffineHom ((baseChange (D.charts a.down).2.projection).obj G).X.hom

local instance bundleCoordinateFintype (a : D.Index) :
    Fintype (D.charts a.down).2.coordinateType := (D.charts a.down).2.coordinateFintype

local instance bundleRootFintype (a : D.Index) :
    Fintype (D.charts a.down).2.rootType := (D.charts a.down).2.rootFintype

/-- The original component open cover is disjoint. -/
lemma groupsOpenCover_isDisjoint : DisjointCoverGluing.IsDisjoint D.groupsOpenCover := by
  intro a b hab
  exact isEmpty_pullback_sigmaι_of_ne
    (fun a : D.Index => Spec (D.charts a.down).2.ring) hab

/-- The actual finite rank of the original exact face-weight layer on a component. -/
def layerRank (d : ℕ) (a : D.Index) : ℕ :=
  Nat.card ((D.charts a.down).2.chart.weights.exactSupport d)

/-- One actual module on the finite cover, with the unchanged separate layer ranks. -/
def layerBundle (d : ℕ) : D.groupsSpace.Modules :=
  DisjointFreeBundle.module D.groupsOpenCover D.groupsOpenCover_isDisjoint (D.layerRank d)

/-- The actual layer module has finite local bases with the prescribed varying ranks. -/
lemma layerBundle_isFiniteLocallyFree (d : ℕ) : IsFiniteLocallyFree (D.layerBundle d) :=
  DisjointFreeBundle.isFiniteLocallyFree D.groupsOpenCover
    D.groupsOpenCover_isDisjoint (D.layerRank d)

/-- Actual module pullback to a component recovers its prescribed free layer sheaf. -/
def layerBundlePieceIso (d : ℕ) (a : D.Index) :
    (Scheme.Modules.pullback (D.componentMap a)).obj (D.layerBundle d) ≅
      freeBundle (Spec (D.charts a.down).2.ring) (D.layerRank d a) :=
  DisjointFreeBundle.pieceIso D.groupsOpenCover D.groupsOpenCover_isDisjoint (D.layerRank d) a

/-- The original component group isomorphism supplies natural free-module point charts. -/
def layerComponentFreePoints (d : ℕ) (a : D.Index)
    (T : Over (Spec (D.charts a.down).2.ring)) :
    (T ⟶ ((baseChange (D.componentMap a)).obj (D.layerGroup d)).X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj
        (freeBundle (Spec (D.charts a.down).2.ring) (D.layerRank d a)))) :=
  groupIsoPoints (D.layerComponentIso d a)
    (freeBundle (Spec (D.charts a.down).2.ring) (D.layerRank d a))
    (freeVectorBundlePoints (CommRingCat.of (D.charts a.down).2.ring) (D.layerRank d a)) T

/-- Naturality of the original component free charts on all tests. -/
lemma layerComponentFreePoints_natural (d : ℕ) (a : D.Index)
    (T W : Over (Spec (D.charts a.down).2.ring)) (b : W ⟶ T)
    (x : T ⟶ ((baseChange (D.componentMap a)).obj (D.layerGroup d)).X) :
    (D.layerComponentFreePoints d a W (b ≫ x)).toAdd =
      sectionPullback (freeBundle (Spec (D.charts a.down).2.ring) (D.layerRank d a)) b
        (D.layerComponentFreePoints d a T x).toAdd := by
  exact groupIsoPoints_natural (D.layerComponentIso d a)
    (freeBundle (Spec (D.charts a.down).2.ring) (D.layerRank d a))
    (freeVectorBundlePoints (CommRingCat.of (D.charts a.down).2.ring) (D.layerRank d a))
    (freeVectorBundlePoints_natural (CommRingCat.of (D.charts a.down).2.ring)
      (D.layerRank d a)) T W b x

/-- Natural actual charts of every component in the actual restricted layer module. -/
def layerComponentCharts (d : ℕ) :
    DisjointBundlePoints.ComponentCharts
      (fun a : D.Index => Spec (D.charts a.down).2.ring)
      (D.layerGroup d) (D.layerBundle d) where
  equiv a := moduleIsoPoints (D.layerBundlePieceIso d a) (D.layerComponentFreePoints d a)
  natural a := moduleIsoPoints_natural (D.layerBundlePieceIso d a)
    (D.layerComponentFreePoints d a) (D.layerComponentFreePoints_natural d a)

/-- All-test points of the actual assembled layer are sections of its actual
finite locally free module, with all original component ranks retained. -/
def layerBundlePoints (d : ℕ) (T : Over D.groupsSpace) :
    (T ⟶ (D.layerGroup d).X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj (D.layerBundle d))) :=
  (D.layerComponentCharts d).pointSectionEquiv T

set_option maxRecDepth 2000 in
/-- The actual assembled layer coordinates respect canonical section pullback. -/
lemma layerBundlePoints_natural (d : ℕ) (T W : Over D.groupsSpace) (b : W ⟶ T)
    (x : T ⟶ (D.layerGroup d).X) :
    (D.layerBundlePoints d W (b ≫ x)).toAdd =
      sectionPullback (D.layerBundle d) b (D.layerBundlePoints d T x).toAdd :=
  (D.layerComponentCharts d).pointSectionEquiv_natural T W b x

/-- The actual assembled face layer satisfies the exact vector-bundle additive predicate. -/
theorem isVectorBundleAdditive_layerGroup (d : ℕ) :
    IsVectorBundleAdditive (D.layerGroup d) := by
  let : Smooth (D.layerGroup d).X.hom := D.smooth_layerGroup d
  exact (D.layerComponentCharts d).isVectorBundleAdditive (D.layerBundle_isFiniteLocallyFree d)

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
