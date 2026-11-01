import Langlands.AlgebraicGeometry.Modules.HigherDirectImageVanishingAffineBaseChangeStatement
import Langlands.AlgebraicGeometry.Modules.AffineBaseChangeVanishing
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction

/-! # Vanishing after arbitrary affine base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections

/-- Joint vanishing of higher direct images of a smooth proper line bundle
implies cohomology vanishing after every affine base change. -/
theorem higherDirectImageVanishingAffineBaseChange :
    HigherDirectImageVanishingAffineBaseChangeStatement.{u} := by
  intro X Y f hf hp Q hQ R x n
  let := hf
  let := hp
  refine isZero_relativeCohomology_pullback_of_affineRestricts f Q ?_ x n
  intro V hV k
  apply isZero_relativeCohomology_of_higherDirectImage (f ∣_ V) hV.isoSpec.hom
  intro q
  exact isZero_higherDirectImage_pullback f V Q.obj q (hQ q)

end Langlands.AlgebraicGeometry.Modules
