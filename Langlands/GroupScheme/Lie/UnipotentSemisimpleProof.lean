import Langlands.GroupScheme.Lie.UnipotentTangent
import Langlands.GroupScheme.Lie.UnipotentSemisimpleStatement
import Langlands.GroupScheme.Lie.SemisimpleNilpotentMatrix
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Vanishing of semisimple actual tangent elements of unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Example 17.75, for actual tangent vectors and genuine algebraic
representations, over an arbitrary field and at every field universe. -/
theorem unipotentSemisimpleStatement : UnipotentSemisimpleStatement.{u} := by
  intro k _ G hAff hLFT hU X hX
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G hAff hLFT
  have hz : ρ.tangentMatrix k X = 0 :=
    (hX n ρ).eq_zero_of_isNilpotent
      (ρ.isNilpotent_tangentMatrix_of_isUnipotent hU k X)
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hm : Mono ρ.hom.hom := Over.mono_of_mono_left _
  apply lieKernelTarget_injective ρ k hm
  rw [← ρ.pointKernelEquiv_tangentMatrix k X,
    ← ρ.pointKernelEquiv_tangentMatrix k 1, hz, ρ.tangentMatrix_one]

end Langlands.GroupScheme
