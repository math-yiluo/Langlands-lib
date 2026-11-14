import Langlands.GroupScheme.AffineWeilSmooth
import Langlands.GroupScheme.AffineWeilBaseChange
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso

/-! # Integral models formed by actual affine Weil restriction -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable (A F B : Type u) [CommRing A] [IsDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F]
  [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  (X Y : GroupScheme (Spec (CommRingCat.of B)))
  [IsAffine X.X.left] [Smooth X.X.hom] [IsAffine Y.X.left] [Smooth Y.X.hom]
  {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- Actual restriction of a smooth affine group, with its supplied generic
identification, is a smooth integral model over the restriction base. -/
def affineWeil (e : AffineWeil.BaseChange.source A B F X ≅ G) :
    IntegralModel A F G where
  group := AffineWeil.groupScheme A B X
  affine := isAffineHom_of_isAffine _
  flat := by
    have := AffineWeil.smooth_groupScheme A B X
    infer_instance
  finiteType := inferInstance
  genericIso := e

theorem affineWeil_isSmooth (e : AffineWeil.BaseChange.source A B F X ≅ G) :
    (affineWeil A F B X e).IsSmooth :=
  AffineWeil.smooth_groupScheme A B X

variable {X Y}
  (e : AffineWeil.BaseChange.source A B F X ≅ G)
  (d : AffineWeil.BaseChange.source A B F Y ≅ H)
  (f : X ⟶ Y) {g : G ⟶ H}

/-- Restriction of the original homomorphism extends the generic map whenever
its actual base-changed square with the supplied identifications commutes. -/
def affineWeilHom
    (h : AffineWeil.BaseChange.sourceMap A B F X f ≫ d.hom = e.hom ≫ g) :
    (affineWeil A F B X e).Hom (affineWeil A F B Y d) g where
  hom := AffineWeil.map A B f
  generic_comm := h

/-- Generic rigidity identifies every compatible extension with the restriction
of the original coefficient-ring map. -/
theorem affineWeil_hom_eq
    (h : AffineWeil.BaseChange.sourceMap A B F X f ≫ d.hom = e.hom ≫ g)
    (φ : (affineWeil A F B X e).Hom (affineWeil A F B Y d) g) :
    φ.hom = AffineWeil.map A B f :=
  φ.hom_eq (affineWeilHom A F B e d f h)

variable [IsLocalRing A]

/-- The special-fibre map of every compatible extension is the original
restricted homomorphism base-changed to the actual residue field of A. -/
theorem affineWeil_specialFibreMap_eq
    (h : AffineWeil.BaseChange.sourceMap A B F X f ≫ d.hom = e.hom ≫ g)
    (φ : (affineWeil A F B X e).Hom (affineWeil A F B Y d) g) :
    φ.specialFibreMap =
      AffineWeil.BaseChange.sourceMap A B (IsLocalRing.ResidueField A) X f := by
  change (GroupScheme.baseChange (residueBaseMap A)).map φ.hom = _
  rw [affineWeil_hom_eq A F B e d f h φ]
  rfl

end Langlands.GroupScheme.IntegralModel
