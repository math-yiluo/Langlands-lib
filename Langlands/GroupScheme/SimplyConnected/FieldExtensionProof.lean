import Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # Supplied simply connected covers remain covers after arbitrary field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Simply connected covers are compatible with field extension** (CGP, Corollary
A.4.11(1)). For every field extension `K/k` and every supplied simply connected cover
`π : C ⟶ G` over `k`, the base-changed map `π_K : C_K ⟶ G_K` is a simply connected cover
over `K`, including its universal property for every central isogeny into `G_K`. -/
theorem isSimplyConnectedCover_fieldExtension :
    IsSimplyConnectedCoverFieldExtensionStatement.{u} := by
  intro k K _ _ _ C G π hπ
  have hG := isSemisimpleFieldExtension k K G hπ.isSemisimple
  have hC := isSimplyConnectedFieldExtension k K C hπ.isSimplyConnected
  have hq := centralIsogenyBaseChange _ _ (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    C G π hπ.isCentralIsogeny
  exact ⟨hG, hC, hq, simplyConnectedCentralCoverUniversalProperty K _ _ _ hC hG hq⟩

end Langlands.GroupScheme
