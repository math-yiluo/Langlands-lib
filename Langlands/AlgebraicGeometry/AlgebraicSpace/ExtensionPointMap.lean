import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs

/-!
# Coefficient extension for points and étale charts

The maps on scheme and algebraic-space points for a normed field extension, together
with the base change of finite-type étale charts and their compatibility.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest schemePointTopology ringBaseChange ringPointBaseChangeEquiv
    schemeBaseChangeTopology_proof isEmbedding_schemeChangeRing)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable (K L : Type u) [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L]

variable {K} {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Base change of a finite-type étale chart to a normed extension field. -/
abbrev EtaleFiniteTypeChart.extension (c : EtaleFiniteTypeChart K X) :
    EtaleFiniteTypeChart L (baseChange (Spec.algebraMap K L) X) where
  scheme := ringBaseChange K L c.scheme
  hom := homMk (restrictAtlas (Spec.algebraMap K L) (AlgebraicSpace.hom c.hom))
  isEtale := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h := c.isEtale
    unfold IsEtale at h ⊢
    exact relative_restrictAtlas (g := Spec.algebraMap K L) (@Etale.{u}) h
  locallyOfFiniteType := by
    have := c.locallyOfFiniteType
    change LocallyOfFiniteType (pullback.snd c.scheme.hom (Spec.algebraMap K L))
    infer_instance
  quasiCompact := by
    have := c.quasiCompact
    change QuasiCompact (pullback.snd c.scheme.hom (Spec.algebraMap K L))
    infer_instance

/-- The point map of a base-changed chart under the base-change identification. -/
theorem baseChangeRingPointsEquiv_extension_pointMap (c : EtaleFiniteTypeChart K X)
    (p : RingPoint L (ringBaseChange K L c.scheme) L) :
    baseChangeRingPointsEquiv K L L X ((c.extension L).pointMap p) =
      RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme L).symm
        ((ringPointBaseChangeEquiv K L L c.scheme).symm p)) := by
  rw [baseChangeRingPointsEquiv_apply]
  refine (mapSections_naturality c.hom
    (PointTopology.ringTestRestrictScalarsIso K L L).inv _).trans ?_
  change mapSections c.hom _ (ULift.up _) = mapSections c.hom _ (ULift.up _)
  congr 2

/-- The natural map `U(K) → U_L(L)` for an actual scheme over `K`. -/
def extensionSchemePointMap (U : Over (Spec (CommRingCat.of K))) :
    RingPoint K U K → RingPoint L (ringBaseChange K L U) L :=
  fun u => ringPointBaseChangeEquiv K L L U (RingPoint.changeRing (Algebra.ofId K L) u)

/-- Coefficient extension is a topological embedding on points of any actual scheme. -/
theorem isEmbedding_extensionSchemePointMap (U : Over (Spec (CommRingCat.of K))) :
    @IsEmbedding _ _ (schemePointTopology K U K)
      (schemePointTopology L (ringBaseChange K L U) L) (extensionSchemePointMap L U) := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K U L) := schemePointTopology K U L
  let : TopologicalSpace (RingPoint L (ringBaseChange K L U) L) :=
    schemePointTopology L (ringBaseChange K L U) L
  have hι : IsEmbedding (Algebra.ofId K L) :=
    (algebraMap_isometry K L).isEmbedding
  exact (schemeBaseChangeTopology_proof K L L U).isEmbedding.comp
    (isEmbedding_schemeChangeRing K K L U (Algebra.ofId K L) hι)

/-- The natural map `X(K) → X_L(L)` for an algebraic space over `K`. -/
def extensionPointMap (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    RingPoints K X K → RingPoints L (baseChange (Spec.algebraMap K L) X) L :=
  fun x => (baseChangeRingPointsEquiv K L L X).symm
    (RingPoints.changeRing (Algebra.ofId K L) x)

/-- Coefficient extension commutes with étale chart maps. -/
theorem extensionPointMap_pointMap (c : EtaleFiniteTypeChart K X)
    (u : RingPoint K c.scheme K) :
    extensionPointMap L X (c.pointMap u) =
      (c.extension L).pointMap (extensionSchemePointMap L c.scheme u) := by
  apply (baseChangeRingPointsEquiv K L L X).injective
  rw [extensionPointMap, Equiv.apply_symm_apply, baseChangeRingPointsEquiv_extension_pointMap,
    extensionSchemePointMap, Equiv.symm_apply_apply, EtaleFiniteTypeChart.pointMap,
    RingPoints.changeRing_map]
  rfl

/-- Coefficient extension is continuous on points of every algebraic space for the
étale-chart topologies. No henselian or separation hypothesis is needed. -/
theorem continuous_extensionPointMap :
    @Continuous _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (extensionPointMap L X) := by
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  rw [etaleChartTopology_continuous_iff]
  intro c
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
  let : TopologicalSpace (RingPoint L (c.extension L).scheme L) :=
    schemePointTopology L (c.extension L).scheme L
  have h : extensionPointMap L X ∘ c.pointMap =
      (c.extension L).pointMap ∘ extensionSchemePointMap L c.scheme :=
    funext (extensionPointMap_pointMap L c)
  rw [h]
  exact (c.extension L).continuous_pointMap.comp
    (isEmbedding_extensionSchemePointMap L c.scheme).continuous

end Langlands.AlgebraicGeometry.AlgebraicSpace
