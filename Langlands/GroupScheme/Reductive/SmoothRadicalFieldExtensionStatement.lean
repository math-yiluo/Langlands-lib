import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # Represented unipotent radicals over algebraically closed extensions

The ambient group is smooth and may be nonaffine or disconnected.
This module states the preservation target; it supplies no proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary extensions of algebraically closed fields preserve a supplied
represented unipotent radical in a smooth ambient group, using the existing
fixed-vector unipotence and greatest all-test image predicates. -/
def SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    (P U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P),
    Smooth P.X.hom → IsUnipotentRadical r →
      IsUnipotentRadical
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r)

end Langlands.GroupScheme
