import Langlands.GroupScheme.Rational.SteinbergRootProduct

/-! # Existence of normalized simple-root data over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every supplied split pinning on an actual affine field group admits
whole-root-subgroup parametrizations normalized by its Lie vectors, together
with rational representatives of its simple reflections. -/
def NormalizedRootExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G),
    Nonempty p.NormalizedSimpleRootParametrizations ∧
      Nonempty p.SimpleReflectionRepresentatives

end Langlands.GroupScheme
