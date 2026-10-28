import Langlands.Representation.Classification.BlockTensorLpProof
import Langlands.Representation.Classification.TemperedLpProof

namespace Langlands

universe uF uV

/-- Analytic temperedness of the actual GL block tensor is equivalent to
analytic temperedness of every irreducible admissible factor. -/
theorem glBlockTensorTempered :
    GLBlockTensorTemperedStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  intro V _ _ ρ hρ hadm
  constructor
  · intro h _ _ μ _
    apply (isTemperedModCenter_iff_forall_isLp (B.blockTensor ρ) μ).mpr
    intro ε hε
    apply (glBlockTensorLp p F T n hn B V ρ hρ hadm (2 + ε)
      (le_add_of_nonneg_right hε.le)).mp ?_ μ
    intro i
    exact (T.isTempered_iff_forall_isLp (ρ i)).mp (h i) ε hε
  · intro h i
    apply (T.isTempered_iff_forall_isLp (ρ i)).mpr
    intro ε hε
    apply (glBlockTensorLp p F T n hn B V ρ hρ hadm (2 + ε)
      (le_add_of_nonneg_right hε.le)).mpr ?_ i
    intro _ _ μ _
    exact (isTemperedModCenter_iff_forall_isLp (B.blockTensor ρ) μ).mp (h μ) ε hε

end Langlands
