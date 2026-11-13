import Langlands.AlgebraicGeometry.Deformation.ArtinianDualNumbers

/-! # The augmentation arrow of an Artinian test -/

noncomputable section

universe u

open CategoryTheory Langlands.AlgebraicGeometry.Deformation

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartVersality

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]

/-- The actual augmentation arrow, without a section or coefficient-field choice. -/
def augmentationArrow (A : ArtinianTest k K) : A ⟶ ArtinianTest.residue k K :=
  ArtinianTest.homMk A.augmentation (by ext; rfl)

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartVersality
