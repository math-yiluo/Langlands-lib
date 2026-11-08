import Langlands.GroupScheme.Reductive.SplitCentralIsogenyReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.CentralTorusQuotientProof
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof

/-! # The central split Isogeny Theorem -/

universe u

namespace Langlands.GroupScheme

/-- **Isogeny Theorem, central case** (Milne, *Algebraic Groups* (2017), Theorem 23.9). Every
central isogeny of the root data of two split maximal tori of connected reductive groups over a
field arises from a central isogeny of the groups and a homomorphism of the tori. -/
theorem splitCentralIsogenyExistence : SplitCentralIsogenyExistenceStatement.{u} :=
  splitCentralIsogenyExistence_of_commonTorusIsomorphism rootDatumExistence
    centralIsogenyRootDatumHom splitCentralTorusQuotient splitCommonTorusIsomorphism

end Langlands.GroupScheme
