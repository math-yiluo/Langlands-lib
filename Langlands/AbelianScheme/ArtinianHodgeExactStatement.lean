import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.AffineCechDeRhamStructureH1
import Mathlib.RingTheory.Artinian.Ring

/-! # The degree-one Hodge sequence for an Artinian abelian scheme -/

universe u

open AlgebraicGeometry Langlands.AlgebraicGeometry.AffineCechDeRham

namespace Langlands.AbelianScheme

/-- For an abelian scheme over a local Artinian rational algebra and a finite affine
open cover, the closed-form class map of the degree-one Hodge sequence is injective,
the projection to Čech classes of functions is surjective, and both end modules are
finite free. Exactness in the middle is `AffineCechDeRham.ker_toStructureH1`. -/
def ArtinianHodgeExactStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R] [Algebra ℚ R]
    (B : AbelianScheme (Spec (CommRingCat.of R)))
    (U : Scheme.AffineOpenCover.{u} B.X.left) [Finite U.I₀],
    Function.Injective (closedFormClass B.X.hom U) ∧
      Function.Surjective (toStructureH1 B.X.hom U) ∧
      Module.Finite R (closedForms B.X.hom U) ∧ Module.Free R (closedForms B.X.hom U) ∧
      Module.Finite R (structureH1 B.X.hom U) ∧ Module.Free R (structureH1 B.X.hom U)

end Langlands.AbelianScheme
