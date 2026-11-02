import Langlands.AbelianScheme.Tate.WeilHom0PullbackCoherence
import Langlands.AbelianScheme.RationalIntegralComparison
import Langlands.CategoryTheory.RationalizationMultiples

/-! # Exact integral equations for actual rational dual pullbacks -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualAB" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "pullback0" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB additivity

/-- Pull back an actual integral dual-valued homomorphism using the constructed dual map. -/
def integralDualPullbackHom (f : A ⟶ B) (lamB : B ⟶ DB) : A ⟶ DA :=
  f ≫ lamB ≫ dualAB f

local notation "pullbackZ" => integralDualPullbackHom preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB

/-- The rational construction agrees with rationalizing the actual integral pullback. -/
theorem rationalDualPullbackHom0_homToHom0 (f : A ⟶ B) (lamB : B ⟶ DB) :
    pullback0 (homToHom0 f) (homToHom0 lamB) =
      homToHom0 (pullbackZ f lamB) := by
  simp only [rationalDualPullbackHom0, dualHom0_homToHom0, comp0_homToHom0,
    integralDualPullbackHom, Category.assoc]

/-- Dual pullback is quadratic in the rational homomorphism. -/
theorem rationalDualPullbackHom0_smul_hom (r : ℚ) (f : Hom0 A B) (lamB : Hom0 B DB) :
    pullback0 (r • f) lamB = (r * r) • pullback0 f lamB := by
  simp only [rationalDualPullbackHom0, map_smul, LinearMap.smul_apply, smul_smul]

/-- A supplied integral representative multiplies rational dual pullback by the
square of its original denominator. -/
theorem integralDualPullbackHom_rationalization
    (e : Rationalization.of A ≅ Rationalization.of B)
    (d : RationalIsoIntegralData e) (lamB : B ⟶ DB) :
    homToHom0 (pullbackZ d.hom lamB) =
      ((d.homDenom : ℚ) * (d.homDenom : ℚ)) •
        pullback0 e.hom (homToHom0 lamB) := by
  rw [← rationalDualPullbackHom0_homToHom0 preservation composition unitCoherence
    associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
    MB evaluationB additivity]
  have hd : homToHom0 d.hom = (d.homDenom : ℚ) • e.hom := by
    change Rationalization.ofHom d.hom = (d.homDenom : ℚ) • e.hom
    rw [Int.cast_smul_eq_zsmul]
    exact d.ofHom_hom
  rw [hd, rationalDualPullbackHom0_smul_hom]

/-- The prescribed rational dual-pullback equation is equivalent to exact integral
cross-multiple data for any supplied integral representative, with its denominator squared. -/
theorem rationalDualPullbackMultiple_iff_integralMultipleData
    (q : ℚ) (e : Rationalization.of A ≅ Rationalization.of B)
    (d : RationalIsoIntegralData e) (lamA : A ⟶ DA) (lamB : B ⟶ DB) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivity q e.hom (homToHom0 lamA) (homToHom0 lamB) ↔
    Nonempty (Rationalization.IntegralMultipleData (pullbackZ d.hom lamB) lamA
      (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * q)) := by
  rw [← Rationalization.ofHom_eq_smul_iff_nonempty_integralMultipleData]
  change pullback0 e.hom (homToHom0 lamB) = q • homToHom0 lamA ↔
    homToHom0 (pullbackZ d.hom lamB) =
      (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * q) • homToHom0 lamA
  rw [integralDualPullbackHom_rationalization preservation composition unitCoherence
    associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
    MB evaluationB additivity]
  have hn : (d.homDenom : ℚ) ≠ 0 := Int.cast_ne_zero.mpr d.homDenom_ne_zero
  constructor
  · intro h
    simpa only [smul_smul] using
      congrArg (fun t : Hom0 A DA => ((d.homDenom : ℚ) * (d.homDenom : ℚ)) • t) h
  · intro h
    have h' := congrArg
      (fun t : Hom0 A DA => ((d.homDenom : ℚ) * (d.homDenom : ℚ))⁻¹ • t) h
    have hcancel : ((d.homDenom : ℚ) * (d.homDenom : ℚ))⁻¹ *
        (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * q) = q :=
      inv_mul_cancel_left₀ (mul_ne_zero hn hn) q
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hn hn), one_smul, hcancel] using h'

/-- Produce an exact integral polarization equation for the supplied rational
isomorphism and supplied integral representative, preserving the rational multiplier. -/
def rationalDualIntegralMultipleData
    (q : ℚ) (e : Rationalization.of A ≅ Rationalization.of B)
    (d : RationalIsoIntegralData e) (lamA : A ⟶ DA) (lamB : B ⟶ DB)
    (he : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivity q e.hom (homToHom0 lamA) (homToHom0 lamB)) :
    Rationalization.IntegralMultipleData (pullbackZ d.hom lamB) lamA
      (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * q) :=
  Classical.choice ((rationalDualPullbackMultiple_iff_integralMultipleData preservation
    composition unitCoherence associativity comparison symmetry stability hA hB geometryA
    geometryB MA evaluationA MB evaluationB additivity q e d lamA lamB).mp he)

end Langlands.AbelianScheme
