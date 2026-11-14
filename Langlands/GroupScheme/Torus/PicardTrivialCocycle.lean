import Langlands.AlgebraicGeometry.Modules.UnitCocyclePicardTrivial
import Langlands.GroupScheme.Torus.LocalCocycle

/-! # Split-torus cocycles over a Picard-trivial affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
  {I : Type u} [Finite I] {U : Over (Spec R)}
  [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
  (ξ : Cocycle (splitTorus (Spec R) I) U)

/-- Choose a split-torus cochain by cobounding each unit coordinate. -/
def splitPicardCochain : U ⟶ (splitTorus (Spec R) I).X :=
  (splitTorus.pointsEquiv I U).symm fun i =>
    Langlands.Scheme.Modules.unitCoboundaryOfPicTrivial U.hom (ξ.unitCoordinate i)
      (ξ.unitCoordinate_isNatural i) (ξ.unitCoordinate_isMultiplicative i)

/-- The chosen split-torus cochain cobounds the original cocycle on all tests. -/
theorem splitPicardCochain_spec {Z : Over (Spec R)} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.splitPicardCochain) * (b ≫ ξ.splitPicardCochain)⁻¹ := by
  apply (splitTorus.pointsEquiv I Z).injective
  funext i
  have h := Langlands.Scheme.Modules.unitCoboundaryOfPicTrivial_spec U.hom
    (ξ.unitCoordinate i) (ξ.unitCoordinate_isNatural i) (ξ.unitCoordinate_isMultiplicative i)
    Z.left a.left b.left ((Over.w a).trans (Over.w b).symm)
  rw [ξ.unitCoordinate_eq i Z a.left b.left (Over.w a) (Over.w b)] at h
  rw [show (Over.homMk a.left (Over.w a) : Z ⟶ U) = a from by ext; rfl,
    show (Over.homMk b.left (Over.w b) : Z ⟶ U) = b from by ext; rfl] at h
  simpa [splitTorus.pointsEquiv_naturality, splitPicardCochain,
    splitTorus.unitsRestrict] using h

/-- Split-torus cocycles on affine faithfully flat covers of `Spec R` vanish
when the module Picard group of `R` is trivial. -/
theorem isTrivial_split_of_pic_trivial : ξ.IsTrivial :=
  ⟨ξ.splitPicardCochain, ξ.splitPicardCochain_spec⟩

end Langlands.GroupScheme.Cocycle
