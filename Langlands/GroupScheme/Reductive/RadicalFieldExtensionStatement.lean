import Langlands.GroupScheme.Reductive.Basic

/-! # Trivial unipotent radical under extension of algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For an extension of algebraically closed fields `K / k`, base change of an
actual smooth connected affine group scheme over `k` preserves the published
all-test trivial-unipotent-radical predicate. -/
def AlgebraicallyClosedRadicalFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      HasTrivialUnipotentRadical G →
        HasTrivialUnipotentRadical
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

end Langlands.GroupScheme
