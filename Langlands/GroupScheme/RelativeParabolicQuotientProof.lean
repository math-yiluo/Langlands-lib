import Langlands.GroupScheme.RelativeParabolicQuotientStatement
import Langlands.GroupScheme.RelativeParabolicQuotientConstruction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.SelfNormalizingProperAmbientProof

/-! # Proper quotients of reductive group schemes by parabolic subgroups: proof -/

universe u

namespace Langlands.GroupScheme.RelativeParabolicQuotient

/-- **Proper quotients `G/P` over every ring** (Conrad, *Reductive group schemes*,
Corollary 5.2.8 with Theorem 2.3.6). The published reduction to the parabolic-dynamic and
proper-ambient statements is discharged by their published proofs. -/
theorem existence : ExistenceStatement.{u} :=
  existenceStatement_of_dynamic_and_ambient parabolicDynamic selfNormalizingProperAmbient

end Langlands.GroupScheme.RelativeParabolicQuotient
