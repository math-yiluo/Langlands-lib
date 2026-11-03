import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Hopf spectra and scalar extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HopfCoordinates

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [HopfAlgebra R A]

/-- Extension of scalars of a commutative Hopf algebra. -/
abbrev scalarExtension : CommHopfAlgCat.{u} S :=
  CommHopfAlgCat.of S (S ⊗[R] A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual pullback of a Hopf spectrum is the spectrum of scalar extension. -/
def baseChangeSpecIso :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
        ((hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A))) ≅
      (hopfSpec (CommRingCat.of S)).obj (op (scalarExtension R S A)) := by
  let e := (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S A).asOver (Spec (CommRingCat.of S))
  haveI : IsMonHom e.hom := by
    change IsMonHom ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S A).hom.asOver
      (Spec (CommRingCat.of S)))
    infer_instance
  exact Grp.mkIso' e

end Langlands.GroupScheme.HopfCoordinates
