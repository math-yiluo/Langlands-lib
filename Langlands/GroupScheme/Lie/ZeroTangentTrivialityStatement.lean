import Langlands.GroupScheme.Lie.DualNumberKernel
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statement: connected affine groups with zero tangent space -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A connected affine group locally of finite type over a field, with trivial
actual identity tangent kernel, is trivial over every test scheme. -/
def ZeroTangentTrivialityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] [Subsingleton (lieKernel G k)],
    IsIso G.X.hom ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x = 1

end Langlands.GroupScheme
