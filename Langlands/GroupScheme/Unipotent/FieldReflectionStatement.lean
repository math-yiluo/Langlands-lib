import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: unipotence descends along extension of the base field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Unipotence of an affine group scheme is reflected by any extension of its base field. -/
def UnipotentFieldReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsUnipotent ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) → IsUnipotent G

end Langlands.GroupScheme
