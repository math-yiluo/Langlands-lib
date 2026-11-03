import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Descent of affineness along a field extension -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

/-- A scheme over a field `k` is affine if its base change to some extension field `K` of `k`
is affine. This is the field-extension case of fpqc descent of affineness. -/
def FieldExtensionAffineDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)),
    IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) → IsAffine X

end Langlands.AlgebraicGeometry
