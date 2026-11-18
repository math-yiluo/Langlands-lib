import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof

/-! # Coherence of analytification restrictions -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.OpenGluing

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- Restriction on a chart to itself is the identity. -/
theorem restriction_refl (U : X.affineOpens)
    (a : CoordinateRing (structureMap f U)) :
    restriction f (show (U : X.Opens) ≤ U from le_rfl) a = a := by
  change (X.homOfLE (show (U : X.Opens) ≤ U from le_rfl)).appTop a = a
  simp only [Scheme.homOfLE_rfl, Scheme.Hom.id_appTop]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- Restrictions compose. -/
theorem restriction_trans {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U)
    (hWV : (W : X.Opens) ≤ V) (a : CoordinateRing (structureMap f U)) :
    restriction f hWV (restriction f hVU a) = restriction f (hWV.trans hVU) a := by
  change ((X.homOfLE hVU).appTop ≫ (X.homOfLE hWV).appTop) a = _
  rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]
  rfl

/-- The analytic restriction on a chart to itself is the identity. -/
theorem localMap_refl (U : X.affineOpens) (y : LocalSpace K f U) :
    localMap K f (show (U : X.Opens) ≤ U from le_rfl) y = y := by
  apply AffineAnalytification.SeminormComparison.pointSeminorm_injective K
    (chartPresentation K f U)
  ext a
  rw [localMap, AffineAnalytification.pointSeminorm_baseMap, restriction_refl]

/-- The analytic restrictions compose. -/
theorem localMap_trans {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U)
    (hWV : (W : X.Opens) ≤ V) (y : LocalSpace K f W) :
    localMap K f hVU (localMap K f hWV y) = localMap K f (hWV.trans hVU) y := by
  apply AffineAnalytification.SeminormComparison.pointSeminorm_injective K
    (chartPresentation K f U)
  ext a
  change AffineAnalytification.pointSeminorm K (chartPresentation K f U)
    (AffineAnalytification.baseMap K _ _ _ (AffineAnalytification.baseMap K _ _ _ y)) a = _
  rw [AffineAnalytification.pointSeminorm_baseMap,
    AffineAnalytification.pointSeminorm_baseMap, localMap,
    AffineAnalytification.pointSeminorm_baseMap, restriction_trans]

/-- The identity and composition laws for affine-open analytic restrictions. -/
def RestrictionCoherence : Prop :=
  (∀ (U : X.affineOpens) (y : LocalSpace K f U), localMap K f (le_refl U.1) y = y) ∧
  (∀ {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U) (hWV : (W : X.Opens) ≤ V)
    (y : LocalSpace K f W),
    localMap K f hVU (localMap K f hWV y) = localMap K f (hWV.trans hVU) y)

/-- Affine-open restrictions satisfy identity and composition. -/
theorem restrictionCoherence : RestrictionCoherence K f :=
  ⟨localMap_refl K f, localMap_trans K f⟩

end Langlands.Analytic.SchemeAnalytification.OpenGluing
