import Langlands.GroupScheme.Reductive.ReductiveFiniteKernelRepresentationStatement
import Langlands.GroupScheme.Reductive.SemisimpleFiniteKernelExistence
import Langlands.GroupScheme.Reductive.SemisimpleFiniteKernelReductiveProof
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentProof

/-! # Reductivity and semisimple representations with finite kernel -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Over a perfect field a smooth connected affine group is reductive exactly
when it has a semisimple representation with finite scheme-theoretic kernel. -/
theorem reductiveFiniteKernelRepresentation :
    ReductiveFiniteKernelRepresentationStatement.{u} := by
  intro k _ _ G _ _ _
  constructor
  · intro hG
    exact hG.exists_semisimple_finiteKernel
  · rintro ⟨n, ρ, hsem, hfin⟩
    exact isConnectedReductive_of_semisimple_finiteKernel
      semisimpleRepresentationUnipotent G n ρ hsem hfin

end Langlands.GroupScheme
