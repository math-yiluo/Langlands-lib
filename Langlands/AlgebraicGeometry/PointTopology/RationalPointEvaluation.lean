import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! # Evaluation and total disconnectedness of canonical rational points -/

noncomputable section

open CategoryTheory Topology
open _root_.AlgebraicGeometry

universe u v w

namespace Langlands.LocalField

/-- The given valuative topology has a basis of open additive subgroups. -/
theorem valuativeNonarchimedeanRing (R : Type u) [Ring R] [ValuativeRel R]
    [TopologicalSpace R] [IsValuativeTopology R] : NonarchimedeanRing R := by
  convert! ValuativeRel.nonarchimedeanRing R
  exact (ValuativeRel.valuation R).toTopologicalSpace_eq

/-- The supplied topology on any nonarchimedean local field is totally disconnected. -/
theorem nonarchimedeanLocalFieldTotallyDisconnected (F : Type u) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    TotallyDisconnectedSpace F :=
  Langlands.BruhatTits.localField_totallyDisconnectedSpace F

end Langlands.LocalField

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Algebra-map points inherit total disconnectedness from the value ring. -/
theorem AlgPoint.totallyDisconnectedSpace
    (R : Type u) (A : Type v) (S : Type w)
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [TopologicalSpace S] [TotallyDisconnectedSpace S] :
    TotallyDisconnectedSpace (AlgPoint R A S) :=
  AlgPoint.isEmbedding_evaluation.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

variable (R : Type u) [CommRing R] [TopologicalSpace R]
variable (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]

/-- Evaluate an actual identity-test point on every global coordinate, continuously
in the existing canonical topology. -/
def rationalPointEvaluation :
    letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    C(RationalPoint R X, AffineCoordinateRing R X → R) := by
  letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  exact
    ⟨fun p => AlgPoint.evaluation
      (affineSchemePointEquiv R X R (rationalPointEquiv R X p)),
      AlgPoint.continuous_evaluation.comp
        ((affineSchemePointHomeomorph R X R).continuous.comp
          (rationalPointHomeomorph R X).continuous)⟩

@[simp] theorem rationalPointEvaluation_apply (p : RationalPoint R X)
    (a : AffineCoordinateRing R X) :
    rationalPointEvaluation R X p a =
      affineSchemePointEquiv R X R (rationalPointEquiv R X p) a := rfl

/-- Evaluation realizes exactly the canonical rational-point topology as a subspace
of a product of copies of the base ring. -/
theorem isEmbedding_rationalPointEvaluation :
    letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    IsEmbedding (rationalPointEvaluation R X) := by
  let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  exact AlgPoint.isEmbedding_evaluation.comp
    ((affineSchemePointHomeomorph R X R).isEmbedding.comp
      (rationalPointHomeomorph R X).isEmbedding)

/-- Canonical affine rational points over a totally disconnected base are totally
disconnected, without any finite-type or group hypothesis. -/
theorem rationalPoint_totallyDisconnectedSpace [TotallyDisconnectedSpace R] :
    letI : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
    TotallyDisconnectedSpace (RationalPoint R X) := by
  let : TopologicalSpace (RationalPoint R X) := rationalPointTopology R X
  exact (isEmbedding_rationalPointEvaluation R X).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (Y : Over (Spec (CommRingCat.of F))) [IsAffine Y.left]

/-- The canonical points of every affine scheme over an arbitrary nonarchimedean
local field are totally disconnected. -/
theorem rationalPoint_totallyDisconnectedSpace_of_localField :
    letI : TopologicalSpace (RationalPoint F Y) := rationalPointTopology F Y
    TotallyDisconnectedSpace (RationalPoint F Y) := by
  let : TotallyDisconnectedSpace F :=
    Langlands.LocalField.nonarchimedeanLocalFieldTotallyDisconnected F
  exact rationalPoint_totallyDisconnectedSpace F Y

end LocalField

end Langlands.AlgebraicGeometry.PointTopology
