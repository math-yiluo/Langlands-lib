import Langlands.GroupScheme.AffineHopfMorphism
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Coordinate maps from a diagonalizable source to an affine group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- Coordinates of an actual homomorphism from a diagonalizable group use the
standard group algebra on the source side. -/
def diagonalSourceCoordinateMap (f : (Diagonalizable.groupScheme R M).toGrp ⟶ G) :
    AffineCoordinates.hopfAlgebra G ⟶ Diagonalizable.hopfAlgebra R M :=
  (hopfSpec.fullyFaithful.preimage
    ((Diagonalizable.hopfSpecIso R M).hom ≫ f ≫
      (AffineCoordinates.hopfSpecIso G).inv)).unop

/-- Hopf spectrum recovers the original morphism under the canonical
coordinate comparisons. -/
theorem diagonalSourceCoordinateMap_spec
    (f : (Diagonalizable.groupScheme R M).toGrp ⟶ G) :
    (hopfSpec R).map (diagonalSourceCoordinateMap f).op =
      (Diagonalizable.hopfSpecIso R M).hom ≫ f ≫
        (AffineCoordinates.hopfSpecIso G).inv :=
  hopfSpec.fullyFaithful.map_preimage _

/-- Equality of the standard source-coordinate maps detects equality of the
actual group-scheme homomorphisms. -/
theorem diagonalSourceCoordinateMap_injective :
    Function.Injective
      (diagonalSourceCoordinateMap (R := R) (M := M) (G := G)) := by
  intro f g h
  have hm := congrArg (fun φ => (hopfSpec R).map φ.op) h
  rw [diagonalSourceCoordinateMap_spec, diagonalSourceCoordinateMap_spec] at hm
  exact (cancel_epi (Diagonalizable.hopfSpecIso R M).hom).mp
    ((cancel_mono (AffineCoordinates.hopfSpecIso G).inv).mp (by
      simpa only [Category.assoc] using hm))

/-- The underlying bialgebra maps also detect the actual morphisms. -/
theorem eq_of_diagonalSourceCoordinates_eq
    {f g : (Diagonalizable.groupScheme R M).toGrp ⟶ G}
    (h : (diagonalSourceCoordinateMap f).hom = (diagonalSourceCoordinateMap g).hom) :
    f = g :=
  diagonalSourceCoordinateMap_injective (CommHopfAlgCat.hom_ext h)

/-- Surjectivity and an idempotent-generated kernel on standard source
coordinates make the actual group homomorphism an open and closed immersion. -/
theorem open_and_closed_of_diagonalSourceCoordinates
    (f : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (hsurj : Function.Surjective (diagonalSourceCoordinateMap f).hom)
    (hker : ∃ e : AffineCoordinates.hopfAlgebra G, IsIdempotentElem e ∧
      RingHom.ker (diagonalSourceCoordinateMap f).hom.toAlgHom.toRingHom = Ideal.span {e}) :
    IsOpenImmersion f.hom.hom.left ∧ IsClosedImmersion f.hom.hom.left := by
  let φ : CommRingCat.of (AffineCoordinates.hopfAlgebra G) ⟶
      CommRingCat.of (AddMonoidAlgebra R M) :=
    CommRingCat.ofHom (diagonalSourceCoordinateMap f).hom.toAlgHom.toRingHom
  have hop : IsOpenImmersion (Spec.map φ) :=
    (isOpenImmersion_SpecMap_iff_of_surjective φ hsurj).mpr hker
  have hcl : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_surjective φ hsurj
  have he : f = (Diagonalizable.hopfSpecIso R M).inv ≫
      (hopfSpec R).map (diagonalSourceCoordinateMap f).op ≫
        (AffineCoordinates.hopfSpecIso G).hom := by
    rw [diagonalSourceCoordinateMap_spec]
    simp
  rw [he]
  change IsOpenImmersion
      ((Diagonalizable.hopfSpecIso R M).inv.hom.hom.left ≫ Spec.map φ ≫
        (AffineCoordinates.hopfSpecIso G).hom.hom.hom.left) ∧
    IsClosedImmersion
      ((Diagonalizable.hopfSpecIso R M).inv.hom.hom.left ≫ Spec.map φ ≫
        (AffineCoordinates.hopfSpecIso G).hom.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  constructor <;> infer_instance

end Langlands.GroupScheme.CompleteLocalDeformation
