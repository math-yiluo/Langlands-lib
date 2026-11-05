import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.GroupScheme.AffineHopfCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual affine group morphisms and their Hopf maps over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineHopfMorphism

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  [IsAffine H.X.left] [IsAffine G.X.left]

/-- The contravariant Hopf map of an actual affine group homomorphism, without
a field hypothesis on the base ring. -/
def pullback (f : H ⟶ G) :
    AffineCoordinates.hopfAlgebra G ⟶ AffineCoordinates.hopfAlgebra H :=
  (hopfSpec.fullyFaithful.preimage
    ((AffineCoordinates.hopfSpecIso H).hom ≫ f ≫
      (AffineCoordinates.hopfSpecIso G).inv)).unop

/-- The Hopf spectrum of the coordinate map is the original homomorphism
under the actual affine coordinate isomorphisms. -/
theorem pullback_map (f : H ⟶ G) :
    (hopfSpec R).map (pullback f).op =
      (AffineCoordinates.hopfSpecIso H).hom ≫ f ≫
        (AffineCoordinates.hopfSpecIso G).inv :=
  hopfSpec.fullyFaithful.map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- Closed immersion is exactly surjectivity on Hopf coordinates over every
commutative base ring. -/
theorem isClosedImmersion_iff_surjective (f : H ⟶ G) :
    IsClosedImmersion f.hom.hom.left ↔ Function.Surjective (pullback f).hom := by
  let eH := AffineCoordinates.hopfSpecIso H
  let eG := AffineCoordinates.hopfSpecIso G
  let φ : CommRingCat.of (AffineCoordinates.hopfAlgebra G) ⟶
      CommRingCat.of (AffineCoordinates.hopfAlgebra H) :=
    CommRingCat.ofHom (pullback f).hom.toAlgHom.toRingHom
  let heH : IsIso eH.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eH.hom
  let heG : IsIso eG.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eG.inv
  let heH' : IsIso eH.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eH.inv
  let heG' : IsIso eG.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eG.hom
  constructor
  · intro hf
    let := hf
    have hc : IsClosedImmersion (Spec.map φ) := by
      change IsClosedImmersion
        (((hopfSpec R).map (pullback f).op).hom.hom.left)
      rw [pullback_map]
      change IsClosedImmersion
        (eH.hom.hom.hom.left ≫ f.hom.hom.left ≫ eG.inv.hom.hom.left)
      infer_instance
    let := hc
    exact CentralExtensionHopfSpec.surjective_of_isClosedImmersion φ
  · intro hf
    let hc : IsClosedImmersion (Spec.map φ) :=
      IsClosedImmersion.spec_of_surjective φ hf
    have he : f = eH.inv ≫ (hopfSpec R).map (pullback f).op ≫ eG.hom := by
      rw [pullback_map]
      change f = eH.inv ≫ (eH.hom ≫ f ≫ eG.inv) ≫ eG.hom
      simp
    rw [he]
    change IsClosedImmersion
      (eH.inv.hom.hom.left ≫ (Spec.map φ) ≫ eG.hom.hom.hom.left)
    exact IsClosedImmersion.comp _ _

end Langlands.GroupScheme.AffineHopfMorphism
