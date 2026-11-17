import Langlands.GroupScheme.Reductive.LocalRankOneCentralizer
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Reductivity and maximal tori of actual relative cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (v : I → ℤ)
  (hG : IsReductive G)

/-- The actual centralizer equipped with its reductivity certificate. -/
def reductiveModel : {L : GroupScheme (Spec (CommRingCat.of R)) // IsReductive L} :=
  ⟨groupScheme I G i v, isReductive i v hG⟩

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
