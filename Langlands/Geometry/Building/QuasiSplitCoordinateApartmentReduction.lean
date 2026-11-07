import Langlands.Geometry.Building.QuasiSplitCoordinateApartmentStatement
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement
import Langlands.Geometry.Building.CentralizerDatumOfStructure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Actual quasi-split apartments from root coordinates and central split tori -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **Assembly of actual quasi-split apartments.** If rational characters of
connected reductive groups are detected on central split tori, and every
actual centralizer datum of a maximal split torus admits an apartment class
with a member described by root coordinates of the three types, then every
maximal split torus of a quasi-split group over a henselian field with a
surjective integer-valued valuation has an actual apartment class with full
centralizer compatibility. The centralizer datum comes from the proved
connected reductivity of dynamic centralizers. -/
theorem quasiSplitIntegerApartmentExistence_of_coordinates
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hcoord : QuasiSplitCoordinateApartmentStatement.{u}) :
    QuasiSplitIntegerApartmentExistenceStatement.{u} := by
  intro k _ v hv hH G _ hQS S i hi
  have := mono_of_isMaximalSplitTorus hi
  have : IsAffineHom S.toGrp.X.hom := hi.isSplitSubtorus.1.isAffineHom
  have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  obtain ⟨C⟩ := CentralizerDatum.nonempty_of_structure dynamicCentralizerReductive hCST
    hQS.isConnectedReductive i hi
  obtain ⟨D, φ, hφ, hc⟩ := hcoord k v hv hH G hQS S i hi C
  exact ⟨D, C, IntegerValuation.isOmegaCompatible_of_rootCoordinateTypes hH hφ hc⟩

end Langlands.Geometry.Building
