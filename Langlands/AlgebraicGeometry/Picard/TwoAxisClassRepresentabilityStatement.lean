import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Representability of the two-axis class presheaf over noetherian affine bases -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every abelian scheme over the spectrum of a noetherian ring, the published
presheaf of compatible two-axis-rigidified line-bundle classes on the whole slice
category is represented by a separated, locally finite type, formally unramified
scheme over the base. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassRepresentabilityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of R)),
      Nonempty ((TwoAxisRigidifiedLineBundle.classPresheaf A).RepresentableBy
        (Over.mk q)) ∧
        IsSeparated q ∧ LocallyOfFiniteType q ∧ FormallyUnramified q

end Langlands.AlgebraicGeometry.Picard
