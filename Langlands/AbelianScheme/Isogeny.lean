import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Finite flat surjective homomorphisms of group schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The underlying scheme-morphism property used for relative isogenies. -/
def isogenyProperty : MorphismProperty Scheme.{u} :=
  @IsFinite ⊓ (@Flat ⊓ @Surjective)

/-- The finite-flat-surjective convention for an isogeny over an arbitrary base.
For abelian schemes this is applied to their underlying group-scheme homomorphism. -/
def IsIsogeny {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H) : Prop :=
  isogenyProperty f.hom.hom.left

end Langlands.GroupScheme
