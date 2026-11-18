import Langlands.GroupScheme.RelativeUnipotent.DisjointCoverSections
import Langlands.GroupScheme.RelativeUnipotent.VectorBundleBaseChangeCocycle
import Langlands.GroupScheme.Descent.DisjointComponentHoms
import Langlands.GroupScheme.RelativeUnipotent.LinearModuleChartDescent

/-! # All-test module charts from actual coproduct components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open Langlands.AlgebraicGeometry.Picard
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.DisjointBundlePoints

variable {I : Type u} (Z : I → Scheme.{u})

local instance pointDecomposition : IsIso (Sigma.desc (Sigma.ι Z)) := by
  rw [Sigma.desc_ι]
  infer_instance

/-- The test on a given actual coproduct component. -/
abbrev componentTest (T : Over (∐ Z)) (i : I) : Over (Z i) :=
  (Over.pullback (Sigma.ι Z i)).obj T

/-- The same component test, read over the coproduct base. -/
abbrev componentOver (T : Over (∐ Z)) (i : I) : Over (∐ Z) :=
  (Over.map (Sigma.ι Z i)).obj (componentTest Z T i)

/-- The original inclusion from a component inverse image into the test. -/
def componentMap (T : Over (∐ Z)) (i : I) : componentOver Z T i ⟶ T :=
  (Over.mapPullbackAdj (Sigma.ι Z i)).counit.app T

/-- A point restricted to the actual group over a component. -/
abbrev restrictedPoint (V : GroupScheme (∐ Z)) (T : Over (∐ Z)) (i : I)
    (x : T ⟶ V.X) :
    componentTest Z T i ⟶ ((baseChange (Sigma.ι Z i)).obj V).X :=
  (Over.pullback (Sigma.ι Z i)).map x

/-- Restricting an original point and forgetting the pullback recovers its
composition with the original component inclusion. -/
lemma point_restriction (V : GroupScheme (∐ Z)) (T : Over (∐ Z))
    (x : T ⟶ V.X) (i : I) :
    baseChangePointsEquiv (Sigma.ι Z i) V (componentTest Z T i)
      (restrictedPoint Z V T i x) = componentMap Z T i ≫ x := by
  apply Over.OverMorphism.ext
  simp [componentMap, Over.pullback_map_left, Over.mapPullbackAdj_counit_app,
    baseChangePointsEquiv_left]

/-- Group points are exactly families of the actual component-pullback points. -/
def pointsEquiv (V : GroupScheme (∐ Z)) (T : Over (∐ Z)) :
    (T ⟶ V.X) ≃* ∀ i, componentTest Z T i ⟶ ((baseChange (Sigma.ι Z i)).obj V).X where
  toFun x i := restrictedPoint Z V T i x
  invFun a := Descent.DisjointComponents.overHom (Sigma.ι Z) a
  left_inv x := Descent.DisjointComponents.overHom_ext (Sigma.ι Z)
    (fun i => Descent.DisjointComponents.map_overHom (Sigma.ι Z) _ i)
  right_inv a := funext (Descent.DisjointComponents.map_overHom (Sigma.ι Z) a)
  map_mul' x y := by
    funext i
    apply (baseChangePointsEquiv (Sigma.ι Z i) V (componentTest Z T i)).injective
    change baseChangePointsEquiv (Sigma.ι Z i) V (componentTest Z T i)
        (restrictedPoint Z V T i (x * y)) =
      baseChangePointsEquiv (Sigma.ι Z i) V (componentTest Z T i)
        (restrictedPoint Z V T i x * restrictedPoint Z V T i y)
    rw [map_mul, point_restriction, point_restriction, point_restriction,
      MonObj.comp_mul]

/-- The actual disjoint open cover of the test by its component inverse images. -/
def testCover (T : Over (∐ Z)) : T.left.OpenCover.{u} :=
  (sigmaOpenCover Z).pullback₁ T.hom

/-- Distinct inverse images of coproduct components have empty overlap. -/
lemma testCover_isDisjoint (T : Over (∐ Z)) :
    DisjointCoverGluing.IsDisjoint (testCover Z T) := by
  intro i j hij
  have := isEmpty_pullback_sigmaι_of_ne Z hij
  exact Function.isEmpty
    (pullback.map (pullback.fst T.hom (Sigma.ι Z i))
      (pullback.fst T.hom (Sigma.ι Z j)) (Sigma.ι Z i) (Sigma.ι Z j)
      (pullback.snd T.hom (Sigma.ι Z i)) (pullback.snd T.hom (Sigma.ι Z j))
      T.hom pullback.condition pullback.condition)

/-- Composition of module pullback on each component, retaining the original
over-scheme structure of the component test. -/
def componentSectionIso (M : (∐ Z).Modules) (T : Over (∐ Z)) (i : I) :
    (Scheme.Modules.pullback ((componentMap Z T i).left)).obj
        ((Scheme.Modules.pullback T.hom).obj M) ≅
      (Scheme.Modules.pullback (componentOver Z T i).hom).obj M :=
  compIso (componentMap Z T i).left T.hom (componentOver Z T i).hom
    (Over.w (componentMap Z T i)) M

/-- Sections on an arbitrary test are the component relative sections, with
the canonical composition comparisons. -/
def sectionsEquiv (M : (∐ Z).Modules) (T : Over (∐ Z)) :
    GlobalSections ((Scheme.Modules.pullback T.hom).obj M) ≃+
      ∀ i, GlobalSections ((Scheme.Modules.pullback (componentOver Z T i).hom).obj M) :=
  (DisjointCoverSections.equiv (testCover Z T) (testCover_isDisjoint Z T)
    ((Scheme.Modules.pullback T.hom).obj M)).trans
      (AddEquiv.piCongrRight (fun i =>
        LinearModuleCharts.sectionIsoEquiv (componentSectionIso Z M T i)))

@[simp]
lemma sectionsEquiv_apply (M : (∐ Z).Modules) (T : Over (∐ Z))
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) (i : I) :
    sectionsEquiv Z M T s i = sectionPullback M (componentMap Z T i) s := rfl

/-- The component inverse-image inclusion is natural in the original test. -/
lemma componentMap_natural {T W : Over (∐ Z)} (b : W ⟶ T) (i : I) :
    (Over.map (Sigma.ι Z i)).map ((Over.pullback (Sigma.ι Z i)).map b) ≫
        componentMap Z T i = componentMap Z W i ≫ b :=
  (Over.mapPullbackAdj (Sigma.ι Z i)).counit.naturality b

/-- Natural all-test charts of the actual restricted groups in the actual
restricted module, on each coproduct component. -/
structure ComponentCharts (V : GroupScheme (∐ Z)) (M : (∐ Z).Modules) where
  equiv : ∀ (i : I) (T : Over (Z i)),
    (T ⟶ ((baseChange (Sigma.ι Z i)).obj V).X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj
        ((Scheme.Modules.pullback (Sigma.ι Z i)).obj M)))
  natural : ∀ (i : I) (T W : Over (Z i)) (b : W ⟶ T)
    (x : T ⟶ ((baseChange (Sigma.ι Z i)).obj V).X),
    (equiv i W (b ≫ x)).toAdd =
      sectionPullback ((Scheme.Modules.pullback (Sigma.ι Z i)).obj M) b
        (equiv i T x).toAdd

namespace ComponentCharts

variable {Z} {V : GroupScheme (∐ Z)} {M : (∐ Z).Modules}
  (C : ComponentCharts Z V M)

/-- Component section coordinates, including the canonical scalar-base
composition comparison. -/
def coordinateEquiv (T : Over (∐ Z)) (i : I) :
    (componentTest Z T i ⟶ ((baseChange (Sigma.ι Z i)).obj V).X) ≃*
      Multiplicative
        (GlobalSections ((Scheme.Modules.pullback (componentOver Z T i).hom).obj M)) :=
  (C.equiv i (componentTest Z T i)).trans
    (AddEquiv.toMultiplicative
      (baseChangeSectionEquiv (Sigma.ι Z i) M (componentTest Z T i)))

/-- The multiplicative form of the actual section decomposition. -/
def sectionProductEquiv (T : Over (∐ Z)) :
    Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) ≃*
      ∀ i, Multiplicative
        (GlobalSections ((Scheme.Modules.pullback (componentOver Z T i).hom).obj M)) :=
  (AddEquiv.toMultiplicative (sectionsEquiv Z M T)).trans
    (MulEquiv.piMultiplicative _)

/-- The assembled point/section equivalence on every original test scheme. -/
def pointSectionEquiv (T : Over (∐ Z)) :
    (T ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :=
  ((pointsEquiv Z V T).trans
    (MulEquiv.piCongrRight (C.coordinateEquiv T))).trans
      (sectionProductEquiv T).symm

set_option maxRecDepth 2000 in
/-- The assembled equivalence recovers the prescribed actual component chart. -/
lemma pointSectionEquiv_component (T : Over (∐ Z)) (x : T ⟶ V.X) (i : I) :
    sectionPullback M (componentMap Z T i) (C.pointSectionEquiv T x).toAdd =
      (C.coordinateEquiv T i (restrictedPoint Z V T i x)).toAdd := by
  have H := (sectionProductEquiv (Z := Z) (M := M) T).apply_symm_apply
    ((MulEquiv.piCongrRight (C.coordinateEquiv T)) (pointsEquiv Z V T x))
  exact congrArg (fun y => (y i).toAdd) H

/-- The assembled charts are natural for the canonical pullback of sections
of the same fixed module sheaf. -/
lemma pointSectionEquiv_natural (T W : Over (∐ Z)) (b : W ⟶ T) (x : T ⟶ V.X) :
    (C.pointSectionEquiv W (b ≫ x)).toAdd =
      sectionPullback M b (C.pointSectionEquiv T x).toAdd := by
  apply (sectionsEquiv Z M W).injective
  funext i
  simp only [sectionsEquiv_apply, C.pointSectionEquiv_component]
  let a := (Over.pullback (Sigma.ι Z i)).map b
  have H :
      (C.coordinateEquiv W i (restrictedPoint Z V W i (b ≫ x))).toAdd =
        sectionPullback M ((Over.map (Sigma.ι Z i)).map a)
          (C.coordinateEquiv T i (restrictedPoint Z V T i x)).toAdd := by
    change baseChangeSectionEquiv (Sigma.ι Z i) M (componentTest Z W i)
        (C.equiv i (componentTest Z W i)
          ((Over.pullback (Sigma.ι Z i)).map (b ≫ x))).toAdd = _
    rw [Functor.map_comp, C.natural, baseChangeSectionEquiv_naturality]
    rfl
  rw [H, ← C.pointSectionEquiv_component, sectionPullback_comp,
    componentMap_natural, ← sectionPullback_comp]

include C in
/-- Natural actual component charts give the exact vector-bundle additive
predicate for the original group over the coproduct base. -/
theorem isVectorBundleAdditive [IsAffineHom V.X.hom] [Smooth V.X.hom]
    (hM : IsFiniteLocallyFree M) : IsVectorBundleAdditive V :=
  ⟨inferInstance, inferInstance, M, hM, C.pointSectionEquiv,
    C.pointSectionEquiv_natural⟩

end ComponentCharts
end Langlands.GroupScheme.RelativeUnipotent.DisjointBundlePoints
