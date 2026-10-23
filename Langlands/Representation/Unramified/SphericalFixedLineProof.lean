import Langlands.Representation.Unramified.SphericalClassificationStatement
import Langlands.Representation.Unramified.SphericalHeckeCommutativity
import Langlands.Representation.Hecke.CommutativeCornerFixedLine

/-! # The actual spherical fixed space of an irreducible admissible object is a line -/

noncomputable section

namespace Langlands.Unramified

open Correspondence

universe uF uV

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup heckeGeneralLinearMeasurable heckeGeneralLinearBorel

/-- A nonzero `GL_(r+1)(O_F)`-fixed space of an actual irreducible admissible smooth
representation of `GL_(r+1)(F)` has complex dimension one. -/
theorem sphericalFixedLine : SphericalFixedLineStatement.{uF, uV} := by
  intro p _ F r A h0
  exact @Hecke.finrank_fixedVectors_eq_one_of_corner_comm (GeneralLinear (r + 1) F.Carrier) _
    (F.canonicalGeneralLinearTopology (r + 1)) (F.canonicalGeneralLinearTopologicalGroup (r + 1))
    _ _ (sphericalHaar F r) _ _ _ _ A.obj.representation A.obj.isSmooth
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r)
    (sphericalHeckeAlgebra_mul_comm F r) A.property.1
    (A.property.2.2 (sphericalOpenSubgroup F r)) h0

end Langlands.Unramified
