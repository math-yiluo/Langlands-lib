import Langlands.Representation.Tensor.SmoothSubquotients
import Langlands.Representation.Parabolic.RefinedJacquetTensor

/-! Actual smooth occurrences in refined Jacquet modules of external tensors. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem suppliedTopologyRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Bundle the actual normalized refined tensor comparison as a smooth
isomorphism, with its precise common-group pullback. -/
def refinedJacquetExternalIso :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (T.normalizedRefinedJacquetFunctor B S).obj (FiniteTensor.externalSmoothObject A) ≅
        SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier B S).symm
          (FiniteTensor.externalSmoothObject
            (fun i => (T.normalizedJacquetFunctor (S i)).obj (A i))) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro A
  exact SmoothRep.mkIso (RefinedJacquetTensor.jacquetEquiv T B S (fun i => (A i).obj))

/-- An occurrence in the actual refined Jacquet module of a coarse tensor is
equivalent to its occurrence in the external tensor of the block Jacquets. -/
theorem subquotient_refinedJacquet_external_iff :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (D : ∀ i, SmoothRep.{0, uF, uV} ℂ ((S i).Levi F.Carrier)),
      SmoothRep.IsSubquotient
        (SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier B S).symm
          (FiniteTensor.externalSmoothObject D))
        ((T.normalizedRefinedJacquetFunctor B S).obj
          (FiniteTensor.externalSmoothObject A)) ↔
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject D)
        (FiniteTensor.externalSmoothObject
          (fun i => (T.normalizedJacquetFunctor (S i)).obj (A i))) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro A D
  constructor
  · intro h
    exact (SmoothRep.isSubquotient_pullback_iff
      (refinedLeviEquivContinuous F.Carrier B S).symm).mp
      (h.of_iso_right (refinedJacquetExternalIso T B S A))
  · intro h
    exact (h.pullback (refinedLeviEquivContinuous F.Carrier B S).symm).of_iso_right
      (refinedJacquetExternalIso T B S A).symm

/-- Irreducible block factors in a refined occurrence occur in the
corresponding actual normalized block Jacquet modules. -/
theorem subquotient_factor_of_refinedJacquet_external :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (D : ∀ i, SmoothRep.{0, uF, uV} ℂ ((S i).Levi F.Carrier)),
      (∀ i, (D i).IsIrreducible) →
      SmoothRep.IsSubquotient
        (SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier B S).symm
          (FiniteTensor.externalSmoothObject D))
        ((T.normalizedRefinedJacquetFunctor B S).obj
          (FiniteTensor.externalSmoothObject A)) →
      ∀ i, SmoothRep.IsSubquotient (D i)
        ((T.normalizedJacquetFunctor (S i)).obj (A i)) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro A D hD h
  exact FiniteTensor.isSubquotient_smooth_factor_of_external hD
    ((subquotient_refinedJacquet_external_iff T B S A D).mp h)

/-- Factorwise actual block Jacquet occurrences reassemble in the refined
Jacquet module of the entire coarse tensor. -/
theorem subquotient_refinedJacquet_external_of_factors :
    letI := T.topology
    letI := suppliedTopologyRing T
    ∀ (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (D : ∀ i, SmoothRep.{0, uF, uV} ℂ ((S i).Levi F.Carrier)),
      (∀ i, SmoothRep.IsSubquotient (D i)
        ((T.normalizedJacquetFunctor (S i)).obj (A i))) →
      SmoothRep.IsSubquotient
        (SmoothRep.pullback (refinedLeviEquivContinuous F.Carrier B S).symm
          (FiniteTensor.externalSmoothObject D))
        ((T.normalizedRefinedJacquetFunctor B S).obj
          (FiniteTensor.externalSmoothObject A)) := by
  let := T.topology
  let := suppliedTopologyRing T
  intro A D h
  exact (subquotient_refinedJacquet_external_iff T B S A D).mpr
    (FiniteTensor.isSubquotient_external h)

end Langlands.Parabolic
