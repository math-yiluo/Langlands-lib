import Langlands.Geometry.Building.MaximalUnramifiedAffineWeylStatement
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof

/-! # Affine roots and affine Weyl containment over the maximal unramified field -/

noncomputable section

universe u

open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The exact affine-root-system and affine-Weyl statement over the maximal
unramified extension, including rank zero. -/
theorem maximalUnramifiedAffineWeyl :
    MaximalUnramifiedAffineWeylStatement.{u} := by
  intro F _ _ _ _ H _ C
  exact integerValuationAffineWeyl (inertiaFixedField F)
    (MaximalUnramified.valuation F) (MaximalUnramified.exists_order_eq_one F) H C

end Langlands.Geometry.Building
