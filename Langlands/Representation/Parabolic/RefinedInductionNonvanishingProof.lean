import Langlands.Representation.Parabolic.RefinedInductionNonvanishingStatement
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof

/-! Evaluation surjectivity and nonvanishing of the actual refined induction. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- A compact local section realizes each prescribed value at identity. -/
theorem normalizedRefinedInductionNonvanishing :
    NormalizedRefinedInductionNonvanishingStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B S
  let := T.leviTopologicalGroup B
  intro V _ _ σ hσ
  let := T.valuativeRel
  let := T.localField
  let := T.leviNonarchimedean B
  let := T.leviLocallyCompactSpace B
  let σP := twist (T.refinedParabolicHalfModulus B S)
    (σ.comp (refinedLeviProjection F.Carrier B S))
  have hσP : IsSmooth σP :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_refinedParabolicHalfModulus B S)).mpr
      (isSmooth_comp _ (refinedLeviProjectionContinuous F.Carrier B S).continuous hσ)
  have hsurj : Function.Surjective
      (fun f : Induction.SmoothFunctions (refinedParabolic F.Carrier B S) σP =>
        Induction.eval (refinedParabolic F.Carrier B S) σP f 1) := by
    intro v
    refine ⟨(Induction.compactLocalSection _ σP hσP 1 v Set.univ
      isOpen_univ (Set.mem_univ _)).val, ?_⟩
    exact Induction.compactLocalSection_apply _ σP hσP 1 v Set.univ
      isOpen_univ (Set.mem_univ _)
  refine ⟨hsurj, ?_⟩
  intro hV
  let := hV
  exact hsurj.nontrivial

end Langlands.Parabolic
