import Langlands.GroupScheme.AffineKernelQuotient
import Langlands.GroupScheme.NormalSubgroupQuotientProof

/-!
# Proof of `Langlands.GroupScheme.NormalSubgroupAffineKernelStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `NormalSubgroupAffineKernelStatement`. -/
theorem normalSubgroupAffineKernel : NormalSubgroupAffineKernelStatement.{u} := by
  intro k _ G _ _ N i hi hn
  obtain ⟨Q, q, hsm, haff, hq⟩ := normalSubgroupQuotient k G N i hi hn
  have := hsm
  exact ⟨Q, q, haff, inferInstance, hq.2.2.2⟩

end Langlands.GroupScheme
