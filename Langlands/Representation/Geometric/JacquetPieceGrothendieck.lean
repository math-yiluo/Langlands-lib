import Langlands.Representation.Geometric.InducedPieceGrothendieck
import Langlands.Representation.Geometric.RefinementUniqueness
import Langlands.Representation.Parabolic.FlattenedJacquetGrothendieck

/-! Actual geometric pieces after Jacquet restriction in flattened coordinates. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Parabolic CuspidalSupport

universe uF uV

/-- With a fixed conjugating permutation and target, the standard source
Levi, including its ordered consecutive block shape, is unique. -/
theorem blockShape_eq_of_conjugatesLevi_same_target
    {F : Type uF} [Field F] {n : ℕ} {K L D : BlockShape n}
    {w : Equiv.Perm (Fin n)}
    (hK : ConjugatesLevi (F := F) K D w)
    (hL : ConjugatesLevi (F := F) L D w) : K = L := by
  apply blockShape_eq_of_leviSubgroup_eq (F := F)
  exact Subgroup.map_injective (MulAut.conj (permutation n F w)).injective
    (hK.trans hL.symm)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ}

/-- Restrict to a standard source shape, transport its whole Levi to the
flattened target refinement, unflatten, and induce inside the target Levi. -/
def jacquetGeometricTerm (K B : BlockShape n) (R : BlockRefinement B)
    (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F.Carrier) K (B.flatten R) w) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (normalizedRefinedInductionK0.{uF, uV} F T B R).comp
    ((flattenedLeviK0.{uF, uV} F.Carrier B R).symm.toLinearMap.comp
      ((leviTransportK0.{uF, uV} F.Carrier K (B.flatten R) w hw).toLinearMap.comp
        (normalizedJacquetK0.{uF, uV} F T K)))

/-- Different constructions of the standard source shape give the same
actual map when the target refinement and permutation agree. -/
theorem jacquetGeometricTerm_eq (K L B : BlockShape n) (R : BlockRefinement B)
    (w : Equiv.Perm (Fin n))
    (hK : ConjugatesLevi (F := F.Carrier) K (B.flatten R) w)
    (hL : ConjugatesLevi (F := F.Carrier) L (B.flatten R) w) :
    jacquetGeometricTerm.{uF, uV} F T K B R w hK =
      jacquetGeometricTerm.{uF, uV} F T L B R w hL := by
  have h := blockShape_eq_of_conjugatesLevi_same_target hK hL
  subst L
  rfl

/-- The actual geometric piece after restriction to its source outer shape
is the uniform flattened term. Both intersection equalities are actual
subgroup equalities; no minimality or positive-rank assumption is needed. -/
theorem geometricPieceK0_comp_jacquetK0
    (C B : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement C) (R : BlockRefinement B)
    (hS : sourceLevi F.Carrier C B w = refinedLevi F.Carrier C S)
    (hR : sourceLevi F.Carrier B C w⁻¹ = refinedLevi F.Carrier B R) :
    letI := T.topology
    (geometricPieceK0.{uF, uV} F T C B w S R hS hR).comp
        (normalizedJacquetK0.{uF, uV} F T C) =
      jacquetGeometricTerm.{uF, uV} F T (C.flatten S) B R w
        (conjugatesLevi_flattened_intersections F.Carrier C B w S R hS hR) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let hw := conjugatesLevi_flattened_intersections F.Carrier C B w S R hS hR
  have hMiddle := flattenedLeviK0_comp_refinedIntersectionTransportK0.{uF, uV}
    F.Carrier C B w S R hS hR hw
  have hJacquet := normalizedFlattenedJacquetK0_eq.{uF, uV} F T C S
  rw [geometricPieceK0_eq_refinedInduction_comp_transport.{uF, uV}
    F T C B w S R hS hR]
  apply LinearMap.ext
  intro x
  change normalizedRefinedInductionK0 F T B R
      (refinedIntersectionTransportK0 F.Carrier C B w S R hS hR
        (normalizedRefinedJacquetK0 F T C S (normalizedJacquetK0 F T C x))) =
    normalizedRefinedInductionK0 F T B R
      ((flattenedLeviK0 F.Carrier B R).symm
        (leviTransportK0 F.Carrier (C.flatten S) (B.flatten R) w hw
          (normalizedJacquetK0 F T (C.flatten S) x)))
  congr 1
  apply (flattenedLeviK0 F.Carrier B R).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun hMiddle
      (normalizedRefinedJacquetK0 F T C S (normalizedJacquetK0 F T C x))).trans
    (congrArg (leviTransportK0 F.Carrier (C.flatten S) (B.flatten R) w hw)
      (LinearMap.congr_fun hJacquet x))

end Langlands.Geometric
