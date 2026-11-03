import Langlands.Global.PositiveRealTorusIntrinsic
import Langlands.Global.PositiveRealIdelesTopology
import Langlands.GroupScheme.MultiplicativePointTopology
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-! # Closed positive-real subgroups of actual adelic torus points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (F : Type u) [Field F]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))

local instance positiveTorusAffinePointsTopology (G : GroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] [TopologicalSpace A] :
    TopologicalSpace (Lie.AffinePoints G A) :=
  GroupScheme.affinePointsTopologicalSpace G (CommAlgCat.of F A)

/-- Actual character evaluation is continuous for the existing regular-function topology. -/
theorem continuous_characterHom
    (A : Type u) [CommRing A] [Algebra F A] [TopologicalSpace A]
    (χ : characterLattice T) :
    Continuous (characterHom F T A χ) :=
  (Gm.continuous_affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F A)).comp
    (GroupScheme.continuous_affinePointsTarget T.toGrp (CommAlgCat.of F A)
      (CommGroupScheme.groupHom χ))

/-- An actual character as a continuous homomorphism on coefficient points. -/
def continuousCharacter
    (A : Type u) [CommRing A] [Algebra F A] [TopologicalSpace A]
    (χ : characterLattice T) :
    Lie.AffinePoints T.toGrp A →ₜ* Aˣ where
  toMonoidHom := characterHom F T A χ
  continuous_toFun := continuous_characterHom F T A χ

variable [NumberField F]

/-- The intrinsic positive subgroup is closed in the actual adelic point topology. -/
theorem isClosed_intrinsicSubgroup :
    IsClosed (intrinsicSubgroup F T : Set (Lie.AffinePoints T.toGrp (Adeles F))) := by
  change IsClosed (↑(⨅ χ : characterLattice T,
    (scalarSubgroup F).comap (characterHom F T (Adeles F) χ)) :
      Set (Lie.AffinePoints T.toGrp (Adeles F)))
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun χ =>
    (PositiveRealIdeles.isClosed_range_full F).preimage
      (continuous_characterHom F T (Adeles F) χ)

/-- The intrinsic positive subgroup, equipped with its proved closedness. -/
def closedIntrinsicSubgroup :
    ClosedSubgroup (Lie.AffinePoints T.toGrp (Adeles F)) where
  toSubgroup := intrinsicSubgroup F T
  isClosed' := isClosed_intrinsicSubgroup F T

variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Every supplied splitting gives the same closed positive-real subgroup. -/
theorem isClosed_subgroup :
    IsClosed (subgroup F I T e : Set (Lie.AffinePoints T.toGrp (Adeles F))) := by
  rw [subgroup_eq_intrinsicSubgroup]
  exact isClosed_intrinsicSubgroup F T

end Langlands.Global.PositiveRealTorus
