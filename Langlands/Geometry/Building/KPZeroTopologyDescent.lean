import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Rational.ScalarExtensionTopology

/-! # Canonical topology and descent of the actual zero subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance kpZeroDescentNormedField : NontriviallyNormedField F := localNormedField F
local instance kpZeroDescentUltrametricDist : IsUltrametricDist F := localNormedField_ultrametric F
local instance kpZeroDescentCompleteSpace : CompleteSpace F := localNormedField_complete F

/-- The actual field inclusion is continuous for the published fixed-field topology. -/
theorem continuous_baseToFixedField :
    @Continuous F (inertiaFixedField F) inferInstance (fixedFieldTopology F)
      (algebraMap F (inertiaFixedField F)) := by
  rw [fixedFieldTopology_eq_induced, continuous_induced_rng]
  let : NontriviallyNormedField (SeparableClosure F) := sepClosureNormedField F
  let : NormedAlgebra F (SeparableClosure F) := spectralNorm.normedAlgebra F (SeparableClosure F)
  exact continuous_algebraMap F (SeparableClosure F)

end Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

open LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]

/-- The existing rational extension map, bundled in exactly the named topologies. -/
def unramifiedRationalExtensionContinuousHom :
    letI : TopologicalSpace (UnramifiedClosure F) := fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
    letI : TopologicalSpace
        (rationalPoints (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)) :=
      rationalPointTopology (UnramifiedClosure F)
        (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M).X
    rationalPoints M →ₜ*
      rationalPoints (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M) := by
  letI : Valued (UnramifiedClosure F) ℝ≥0 := fixedFieldValued F
  letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  letI : TopologicalSpace
      (rationalPoints (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)) :=
    rationalPointTopology (UnramifiedClosure F)
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M).X
  exact
    { toMonoidHom := GaloisPointComparison.rationalExtend F (UnramifiedClosure F) M
      continuous_toFun := GaloisPointComparison.continuous_rationalExtend F
        (UnramifiedClosure F) M (continuous_baseToFixedField F) }

@[simp] theorem unramifiedRationalExtensionContinuousHom_apply (m : rationalPoints M) :
    unramifiedRationalExtensionContinuousHom F M m =
      GaloisPointComparison.rationalExtend F (UnramifiedClosure F) M m := rfl

/-- Openness of the actual unramified zero subgroup descends along the actual
rational extension map. The premise is retained for the later openness proof. -/
theorem isOpen_anisotropicZeroPoints_of_isOpen
    (E : UnramifiedZeroDatum F
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)) :
    letI : TopologicalSpace (UnramifiedClosure F) := fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
    letI : TopologicalSpace
        (rationalPoints (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)) :=
      rationalPointTopology (UnramifiedClosure F)
        (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M).X
    IsOpen (E.zeroPoints : Set (rationalPoints
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M))) →
      IsOpen (anisotropicZeroPoints E : Set (rationalPoints M)) := by
  let : TopologicalSpace (UnramifiedClosure F) := fixedFieldTopology F
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  let : TopologicalSpace
      (rationalPoints (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M)) :=
    rationalPointTopology (UnramifiedClosure F)
      (GaloisPointComparison.baseChanged F (UnramifiedClosure F) M).X
  intro h
  exact h.preimage (unramifiedRationalExtensionContinuousHom F M).continuous

end Langlands.Geometry.Building
