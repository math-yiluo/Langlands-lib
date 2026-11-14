import Langlands.GroupScheme.RelativeUnipotent.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Statement: vector-bundle series imply affine torsor vanishing -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual fpqc torsor under a smooth affine group with a finite
vector-bundle normal series has a section over an arbitrary affine base.
This isolates the vanishing argument in the first paragraph of the proof of
Conrad (2014), Corollary 5.4.8. -/
def RelativeUnipotentAffineTorsorStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (U : GroupScheme S)
    [Smooth U.X.hom] [IsAffineHom U.X.hom],
    RelativeUnipotent.HasFiniteVectorBundleSeries U →
    ∀ (X : Over S) [ModObj U.X X],
      Flat X.hom → Surjective X.hom → QuasiCompact X.hom →
      IsIso (ModObj.leftSMul U.X X) →
      ∃ s : S ⟶ X.left, s ≫ X.hom = 𝟙 S

end Langlands.GroupScheme
