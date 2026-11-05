import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.Global.CurvePlaceCompletedTensorEquiv

/-! # Actual all-upper-place Weil point homeomorphisms for global function fields -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open IsDedekindDomain Langlands.Global
open scoped Langlands.Global.CurvePlaceCompletionExtension

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [FiniteDimensional K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (Y : Over (Spec (CommRingCat.of L))) [LocallyOfFiniteType Y.hom]
  (v : AlgebraicCurve.Place k K)

omit [Finite k] [IsScalarTower k K L] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
private theorem functionFieldFactorIsModuleTopology (q : CurvePlacesAbove k L v) :
    IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) := by
  let : (Valued.v : Valuation (curvePlaceCompletion v)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : NontriviallyNormedField (curvePlaceCompletion v) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- At every actual function-field place, original quasi-projective Weil points
are homeomorphic to the product over every original upper completion. -/
def functionFieldWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace L n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec L n = Y.hom) :
    letI : TopologicalSpace
        (RingPoint K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v)) :=
      schemePointTopology K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v)
    letI : ∀ q : CurvePlacesAbove k L v,
        TopologicalSpace (RingPoint L Y (curvePlaceCompletion q.1)) :=
      fun q => schemePointTopology L Y (curvePlaceCompletion q.1)
    RingPoint K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v, RingPoint L Y (curvePlaceCompletion q.1)) := by
  let : ∀ q : CurvePlacesAbove k L v,
      IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    functionFieldFactorIsModuleTopology k K L v
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Free (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Free.of_divisionRing _ _
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Projective (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Projective.of_free
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    K L (curvePlaceCompletion v) (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlaceCompletedTensorEquiv.allTensorEquiv v)
    (CurvePlaceCompletedTensorEquiv.allTensorEquiv_one_tmul v) Y n j hj

/-- Each upper component is the original Weil counit evaluated on the actual
completed-tensor factor test spectrum. -/
theorem functionFieldWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace L n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec L n = Y.hom)
    (p : RingPoint K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v))
    (q : CurvePlacesAbove k L v) :
    functionFieldWeilRestrictionPointHomeomorph k K L Y v n j hj p q =
      completedTensorWeilRestrictionFactorTestMap K L (curvePlaceCompletion v)
          (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
          (CurvePlaceCompletedTensorEquiv.allTensorEquiv v)
          (CurvePlaceCompletedTensorEquiv.allTensorEquiv_one_tmul v) q ≫
        affineChartWeilRestrictionComparison K L Y (ringTest K (curvePlaceCompletion v)) p := by
  let : ∀ q : CurvePlacesAbove k L v,
      IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    functionFieldFactorIsModuleTopology k K L v
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Free (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Free.of_divisionRing _ _
  let : ∀ q : CurvePlacesAbove k L v,
      Module.Projective (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
    fun _ => Module.Projective.of_free
  have h := projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    K L (curvePlaceCompletion v) (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlaceCompletedTensorEquiv.allTensorEquiv v)
    (CurvePlaceCompletedTensorEquiv.allTensorEquiv_one_tmul v) Y n j hj p q
  let : TopologicalSpace
      (RingPoint K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v)) :=
    schemePointTopology K (affineChartWeilRestriction K L Y) (curvePlaceCompletion v)
  let : ∀ q : CurvePlacesAbove k L v,
      TopologicalSpace (RingPoint L Y (curvePlaceCompletion q.1)) :=
    fun q => schemePointTopology L Y (curvePlaceCompletion q.1)
  have hh : functionFieldWeilRestrictionPointHomeomorph k K L Y v n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        K L (curvePlaceCompletion v) (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (CurvePlaceCompletedTensorEquiv.allTensorEquiv v)
        (CurvePlaceCompletedTensorEquiv.allTensorEquiv_one_tmul v) Y n j hj := rfl
  rw [hh]
  exact h

end Langlands.AlgebraicGeometry.PointTopology
