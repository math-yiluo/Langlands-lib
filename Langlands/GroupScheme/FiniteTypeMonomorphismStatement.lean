import Langlands.GroupScheme.Reductive.Basic

/-! # Monomorphisms of algebraic groups are closed immersions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A scheme monomorphism between separated finite-type group schemes over
an arbitrary field is a closed immersion. -/
def FiniteTypeMonomorphismStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] [IsSeparated H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom.left],
      IsClosedImmersion f.hom.hom.left

end Langlands.GroupScheme
