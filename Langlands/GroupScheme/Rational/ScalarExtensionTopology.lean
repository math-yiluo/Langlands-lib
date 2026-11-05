import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.AffinePointBaseChangeSmooth

/-! # Canonical topology on rational extension of scalars -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The existing rational base-change comparison is the affine comparison
applied after the identity-test transport. -/
theorem baseChangeCoeffEquiv_eq_affineBaseChange
    (p : rationalPoints (baseChanged k L G)) :
    baseChangeCoeffEquiv k L G p =
      (affinePointsBaseChangeMulEquiv k L L G).symm
        (rationalPointEquiv L (baseChanged k L G).X p) := by
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_left, affinePointsBaseChangeMulEquiv_symm_left,
    rationalPointEquiv_left]

variable [IsAffine G.X.left] [TopologicalSpace L] [IsTopologicalRing L]

private instance scalarExtension_isAffine : IsAffine (baseChanged k L G).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback G.X.hom (baseMap k L))
  infer_instance

local instance coefficientPointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of k L)) :=
  G.affinePointsTopologicalSpace _

local instance extendedPointTopology :
    TopologicalSpace ((baseChanged k L G).affinePoints (CommAlgCat.of L L)) :=
  (baseChanged k L G).affinePointsTopologicalSpace _

private def scalarExtensionPointHomeomorph :
    @Homeomorph (rationalPoints (baseChanged k L G))
      (G.affinePoints (CommAlgCat.of k L))
      (rationalPointTopology L (baseChanged k L G).X)
      (G.affinePointsTopologicalSpace (CommAlgCat.of k L)) := by
  letI : TopologicalSpace (rationalPoints (baseChanged k L G)) :=
    rationalPointTopology L (baseChanged k L G).X
  exact (rationalPointsAffineHomeomorph (baseChanged k L G)).trans
    (affinePointsBaseChangeContinuousMulEquiv k L L G).symm.toHomeomorph

/-- The actual pullback comparison preserves the canonical rational-point
and coefficient-evaluation topologies. -/
def baseChangeCoeffContinuousMulEquiv :
    letI : TopologicalSpace (rationalPoints (baseChanged k L G)) :=
      rationalPointTopology L (baseChanged k L G).X
    rationalPoints (baseChanged k L G) ≃ₜ* G.affinePoints (CommAlgCat.of k L) := by
  letI : TopologicalSpace (rationalPoints (baseChanged k L G)) :=
    rationalPointTopology L (baseChanged k L G).X
  have he : (baseChangeCoeffEquiv k L G :
      rationalPoints (baseChanged k L G) → G.affinePoints (CommAlgCat.of k L)) =
      scalarExtensionPointHomeomorph k L G := by
    funext p
    exact baseChangeCoeffEquiv_eq_affineBaseChange k L G p
  have hh : IsHomeomorph (baseChangeCoeffEquiv k L G) := by
    rw [he]
    exact (scalarExtensionPointHomeomorph k L G).isHomeomorph
  exact
    { toMulEquiv := baseChangeCoeffEquiv k L G
      continuous_toFun := hh.continuous
      continuous_invFun := ((baseChangeCoeffEquiv k L G).toEquiv.isHomeomorph_iff.mp hh).2 }

@[simp] theorem baseChangeCoeffContinuousMulEquiv_apply
    (p : rationalPoints (baseChanged k L G)) :
    baseChangeCoeffContinuousMulEquiv k L G p = baseChangeCoeffEquiv k L G p := rfl

variable [TopologicalSpace k]

local instance basePointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace _

/-- A continuous field inclusion induces the published rational extension map
continuously, for precisely the named canonical topologies. -/
theorem continuous_rationalExtend (h : Continuous (algebraMap k L)) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
    letI : TopologicalSpace (rationalPoints (baseChanged k L G)) :=
      rationalPointTopology L (baseChanged k L G).X
    Continuous (rationalExtend k L G) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  let : TopologicalSpace (rationalPoints (baseChanged k L G)) :=
    rationalPointTopology L (baseChanged k L G).X
  have hc : Continuous (rationalCoeffEquiv k G) := by
    convert (rationalPointsAffineHomeomorph G).continuous_toFun using 1
    funext p
    exact rationalCoeffEquiv_eq k G p
  have hm : Continuous (GaloisPoint.extend k L G) :=
    G.continuous_affinePointMap (CommAlgCat.ofHom (Algebra.ofId k L)) h
  exact (baseChangeCoeffContinuousMulEquiv k L G).symm.continuous.comp (hm.comp hc)

end Langlands.GroupScheme.GaloisPointComparison
