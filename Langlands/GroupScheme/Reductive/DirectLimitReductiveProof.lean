import Langlands.GroupScheme.Reductive.DirectLimitAssembly
import Langlands.GroupScheme.Reductive.IdentityComponentSemisimpleLocusProof

/-! # Reductivity and semisimplicity over a direct limit of rings -/

universe u

namespace Langlands.GroupScheme

/-- Reductivity and semisimplicity descend along every directed colimit of rings. -/
theorem directLimitReductive : DirectLimitReductiveStatement.{u} :=
  directLimitReductive_of_semisimpleLocusOpen identityComponentSemisimpleLocusOpen

end Langlands.GroupScheme
