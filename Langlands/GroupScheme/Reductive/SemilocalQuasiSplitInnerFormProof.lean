import Langlands.GroupScheme.Adjoint.RelativeExistenceProof
import Langlands.GroupScheme.Reductive.RelativeQuasiSplitInnerFormProof
import Langlands.GroupScheme.Reductive.SemilocalInnerFormAssembly
import Langlands.GroupScheme.RelativeLevi.AdjointTorusWeilPresentationProof
import Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationProof

/-! # Quasi-split inner forms over semilocal rings -/

universe u

namespace Langlands.GroupScheme

/-- A reductive group scheme over a semilocal ring has a quasi-split inner
form, unique up to isomorphism over the base. -/
theorem reductiveSemilocalQuasiSplitInnerForm :
    ReductiveSemilocalQuasiSplitInnerFormStatement.{u} :=
  reductiveSemilocalQuasiSplitInnerFormStatement_of_geometricPrerequisites
    relativeQuasiSplitInnerFormExistence relativeAdjointQuotientExistence
    relativeUnipotentRadicalFiltration relativeBorelAdjointTorusWeilPresentation

end Langlands.GroupScheme
