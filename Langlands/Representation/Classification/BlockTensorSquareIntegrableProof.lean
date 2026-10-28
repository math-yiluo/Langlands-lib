import Langlands.Representation.Classification.BlockTensorLpProof

/-!
# Square-integrability of actual GL block tensors

Specialize the published common finite-exponent comparison to exponent two.
-/

namespace Langlands

universe uF uV

/-- Every irreducible admissible GL block factor is square-integrable exactly
when the actual tensor is square-integrable for every Borel Haar realization
on the actual Levi quotient by its full center. -/
theorem glBlockTensorSquareIntegrable :
    GLBlockTensorSquareIntegrableStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  intro V _ _ ρ hirr hadm
  have htwo := glBlockTensorLp.{uF, uV} p F T n hn B V ρ hirr hadm 2 le_rfl
  constructor
  · intro hf _ _ μ _
    apply (isLpModCenter_two_iff (B.blockTensor ρ) μ).mp
    exact htwo.mp (fun i => (T.isLp_two_iff (ρ i)).mpr (hf i)) μ
  · intro ht i
    apply (T.isLp_two_iff (ρ i)).mp
    apply htwo.mpr ?_ i
    intro _ _ μ _
    exact (isLpModCenter_two_iff (B.blockTensor ρ) μ).mpr (ht μ)

end Langlands
