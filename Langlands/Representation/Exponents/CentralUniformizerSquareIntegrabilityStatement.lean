import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Langlands.Representation.Plancherel.RenardUniformizerSection
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Category.Basic
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Square integrability modulo the central uniformizer lattice -/

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel

/-- The central uniformizer lattice is closed and cocompact in the full center.
For any Haar measure on each quotient, square integrability modulo this lattice
is equivalent to square integrability modulo the full center. -/
def CentralUniformizerSquareIntegrabilityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
    (ha : IsSplitComponent a),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    haveI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
    let C := RenardCartan.C0 A a
    let Z := Subgroup.center (rationalPoints G)
    let hC : C ≤ Z := by
      change RenardCartan.C0 A a ≤ Subgroup.center _
      rw [RenardCartan.C0_eq_map_CA]
      exact (Subgroup.map_le_range _ _).trans ha.isCentralSplitTorus.isCentral.range_le_center
    haveI : C.Normal := C.normal_of_le_center hC
    IsClosed (C : Set (rationalPoints G)) ∧ CompactSpace (Z ⧸ C.subgroupOf Z) ∧
      ∀ [MeasurableSpace (rationalPoints G ⧸ C)] [BorelSpace (rationalPoints G ⧸ C)]
        [MeasurableSpace (rationalPoints G ⧸ Z)] [BorelSpace (rationalPoints G ⧸ Z)]
        (μC : Measure (rationalPoints G ⧸ C)) [μC.IsHaarMeasure]
        (μZ : Measure (rationalPoints G ⧸ Z)) [μZ.IsHaarMeasure]
        (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        IsSquareIntegrableModCentralSubgroup C hC π.representation μC ↔
          IsSquareIntegrableModCenter π.representation μZ

end Langlands.Aubert.General.RepresentedParabolic
