import Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianPrimitiveTransport
import Langlands.AlgebraicGeometry.Picard.OnePointPicardZeroSquare
import Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingProof

/-! # Artinian lifting of Picard-zero families on abelian schemes -/

universe u

namespace Langlands.AbelianScheme

/-- Artinian lifting of Picard-zero families follows from the lifting of primitive line
bundles along elementary Artinian thickenings. -/
theorem picardZeroArtinianLifting_of_artinianPrimitive
    (hP : ArtinianPrimitiveLineBundleLiftingStatement.{u}) :
    PicardZeroArtinianLiftingStatement.{u} :=
  PicardZeroArtinianLiftingReduction.picardZeroArtinianLifting_of_primitive hP
    (fun B _ _ _ X L hL ↦ OnePointSquare.artinianLocalSquare B X L hL)

/-- Let `A` be an abelian scheme over `S`, let `φ : B' → B` be a surjection of local Artinian
rings whose kernel is killed by the maximal ideal of `B'`, and let `β : Spec B' ⟶ S`. Every
geometric Picard-zero rigidified family on `A` over `Spec B` (viewed over `S` through
`Spec φ ≫ β`) is isomorphic to the rigidified pullback along `Spec φ` of a geometric
Picard-zero rigidified family on `A` over `Spec B'`. -/
theorem picardZeroArtinianLifting : PicardZeroArtinianLiftingStatement.{u} :=
  picardZeroArtinianLifting_of_artinianPrimitive artinianPrimitiveLineBundleLifting

end Langlands.AbelianScheme
