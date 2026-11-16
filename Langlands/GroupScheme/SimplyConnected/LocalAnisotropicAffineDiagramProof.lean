import Langlands.Geometry.Building.LocalAnisotropicAffineDiagramRemainingInputs
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsProof
import Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberProof

/-! # Proof: the affine diagram of an anisotropic group over a local field -/

universe u

namespace Langlands.GroupScheme

/-- **The building part of Kaletha–Prasad Theorem 10.3.1.** For an absolutely almost
simple anisotropic group over a nonarchimedean local field, the absolute Cartan matrix of
every Tits index datum extends to an affine Cartan matrix on `Option d.Vertex` with a
strictly positive integral left-kernel vector and vertex-transitive symmetries. -/
theorem localAnisotropicAffineDiagram : LocalAnisotropicAffineDiagramStatement.{u} :=
  Langlands.Geometry.Building.localAnisotropicAffineDiagram_of_remaining_building_inputs
    Langlands.Geometry.Building.specialTorusExistence
    Langlands.Geometry.Building.quasiSplitIndivisibleDerivativeLifts
    Langlands.Geometry.Building.unramifiedSpecialApartmentChamber

end Langlands.GroupScheme
