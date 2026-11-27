import Langlands.GroupScheme.Lie.AffineBracket

/-! # Tangent Lie algebras over algebras of a base field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

namespace FieldLie

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  (K : Type u) [CommRing K] [Algebra k K]

/-- The bracket on the tangent Lie algebra of a group over a field `k`, with coefficients in a
`k`-algebra `K`. -/
scoped instance lieRing : LieRing (Additive (lieKernel G K)) :=
  instAffineKernelLieRing (R := CommRingCat.of k) (A := K) G

/-- The tangent Lie algebra of a group over a field `k`, with coefficients in a `k`-algebra
`K`. -/
scoped instance lieAlgebra : LieAlgebra K (Additive (lieKernel G K)) :=
  instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := K) G

end FieldLie

end Langlands.GroupScheme.Lie
