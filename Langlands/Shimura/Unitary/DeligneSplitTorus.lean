import Langlands.GroupScheme.Torus.Split
import Langlands.Shimura.Unitary.DeligneSchemeSplitting

/-! # The complex Deligne torus is a split torus of rank two -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace Langlands.Shimura.DeligneTorus

/-- The complex pullback of the real Deligne group scheme is the split torus on two indices:
the existing splitting into `𝔾_m ⊗ 𝔾_m`, followed by the rank-one identifications and the
product comparison. -/
def complexSplitTorusIso :
    complexGroupScheme ≅ GroupScheme.splitTorus (Spec (CommRingCat.of ℂ)) (PUnit ⊕ PUnit) :=
  complexSplitting ≪≫
    (GroupScheme.splitTorus.gmIso _ ⊗ᵢ GroupScheme.splitTorus.gmIso _) ≪≫
    GroupScheme.splitTorus.prodIso PUnit PUnit

/-- The complex pullback of the real Deligne group scheme is a split torus. -/
theorem isSplitTorus_complexGroupScheme : GroupScheme.IsSplitTorus complexGroupScheme :=
  ⟨PUnit ⊕ PUnit, inferInstance, ⟨complexSplitTorusIso⟩⟩

end Langlands.Shimura.DeligneTorus
