import Langlands.GroupScheme.RelativeLevi.FaceQuotientPointRecovery

/-! # Original scalar multiplication in the actual component quotient coordinates -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

/-- The canonical actual free section coordinates preserve their test's scalars. -/
lemma freeBundleSectionEquiv_smul {S : Scheme.{u}} (n : ℕ) (T : Over S)
    (r : Γ(T.left, ⊤)) (x : Fin n → Γ(T.left, ⊤)) :
    freeBundleSectionEquiv n T (r • x) = r • freeBundleSectionEquiv n T x :=
  (freeBundleBasis n T).equivFun.symm.map_smul r x

end Langlands.GroupScheme.RelativeUnipotent

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent RelativeUnipotent.NaturalModuleTransformations

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual canonical normalization of the original component module chart
is a linear equivalence over the test's own global functions. -/
def componentSectionLinearEquiv (d : ℕ) (i : D.Index) {Y : Scheme.{u}}
    (b : Y ⟶ Spec (D.charts i.down).2.ring) :
    GlobalSections ((Scheme.Modules.pullback (b ≫ D.componentMap i)).obj (D.layerBundle d))
      ≃ₗ[Γ(Y, ⊤)] GlobalSections ((Scheme.Modules.pullback b).obj
        (freeBundle (Spec (D.charts i.down).2.ring) (D.layerRank d i))) :=
  (baseChangeLinearEquiv (D.componentMap i) (D.layerBundle d) (Over.mk b)).symm ≪≫ₗ
    sectionLinearEquiv ((Scheme.Modules.pullback b).mapIso (D.layerBundlePieceIso d i))

set_option maxRecDepth 2000 in
/-- This actual linear normalization retains exactly the original global
quotient's vector point chart on every original test. -/
lemma componentSectionLinearEquiv_chart (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    D.componentSectionLinearEquiv d i b
        ((D.globalFaceQuotientCharts r hG hp hr d).equiv T (b ≫ D.componentMap i)
          (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) x).toAdd =
      (freeVectorBundlePoints (CommRingCat.of (D.charts i.down).2.ring)
        (D.layerRank d i) (Over.mk b) (D.quotientComponentPoint r hG hp hr d i T b hb x)).toAdd := by
  change ((Scheme.Modules.pullback b).map (D.layerBundlePieceIso d i).hom).app ⊤
    ((baseChangeLinearEquiv (D.componentMap i) (D.layerBundle d) (Over.mk b)).symm
      ((D.globalFaceQuotientCharts r hG hp hr d).equiv T (b ≫ D.componentMap i)
        (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) x).toAdd) = _
  rw [baseChangeLinearEquiv_symm_apply]
  exact D.globalFaceQuotientCharts_component r hG hp hr d i T b hb x

/-- The original quotient point coordinates on a component faithfully retain
the original global group point. -/
lemma quotientComponentPoint_injective (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom) :
    Function.Injective (D.quotientComponentPoint r hG hp hr d i T b hb) := by
  intro x y h
  apply (LiftedModuleCharts.liftPointsEquiv (D.charts i.down).2.projection
    (D.globalFaceQuotientData r hG hp hr d).group T b hb).injective
  exact (cancel_mono (D.globalFaceQuotientComponentIso r hG hp hr d i).hom.hom.hom).mp h

set_option maxRecDepth 2000 in
/-- The scalar operation of the ORIGINAL lifted module chart is actual scalar
multiplication in the ORIGINAL component vector quotient coordinates. -/
lemma quotientComponentPoint_scaledPoint_sections (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (s : Γ(T.left, ⊤)) (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    (freeVectorBundlePoints (CommRingCat.of (D.charts i.down).2.ring)
      (D.layerRank d i) (Over.mk b)
      (D.quotientComponentPoint r hG hp hr d i T b hb
        ((D.globalFaceQuotientCharts r hG hp hr d).scaledPoint T (b ≫ D.componentMap i)
          (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) s x))).toAdd =
      s • (freeVectorBundlePoints (CommRingCat.of (D.charts i.down).2.ring)
        (D.layerRank d i) (Over.mk b)
        (D.quotientComponentPoint r hG hp hr d i T b hb x)).toAdd := by
  rw [← D.componentSectionLinearEquiv_chart r hG hp hr,
    LiftedModuleCharts.scaledPoint_equiv, map_smul,
    D.componentSectionLinearEquiv_chart]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original scalar operation has the original vector coordinate formula,
with scalars in the actual global functions of an arbitrary test scheme. -/
lemma quotientComponentPoint_scaledPoint_coordinates (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (s : Γ(T.left, ⊤)) (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    (VectorGroup.coordinates (CommRingCat.of (D.charts i.down).2.ring)
      (D.layerRank d i) (Over.mk b)
      (D.quotientComponentPoint r hG hp hr d i T b hb
        ((D.globalFaceQuotientCharts r hG hp hr d).scaledPoint T (b ≫ D.componentMap i)
          (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) s x))).toAdd =
      s • (show Fin (D.layerRank d i) → Γ(T.left, ⊤) from
        (VectorGroup.coordinates (CommRingCat.of (D.charts i.down).2.ring)
          (D.layerRank d i) (Over.mk b)
          (D.quotientComponentPoint r hG hp hr d i T b hb x)).toAdd) := by
  apply (freeBundleSectionEquiv (D.layerRank d i) (Over.mk b)).injective
  rw [freeBundleSectionEquiv_smul]
  exact D.quotientComponentPoint_scaledPoint_sections r hG hp hr d i T b hb s x

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
