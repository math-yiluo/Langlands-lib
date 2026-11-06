import Langlands.GroupScheme.Reductive.Pinning
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Statement: unique lifting of based-root-datum isomorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every based-root-datum equivalence of actual pinned split reductive field
groups lifts to a unique actual pinned group isomorphism. The weight map is
inverse character pullback, and the coweight map is contravariant. -/
def PinnedIsomorphismStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (p : SplitPinning G) (q : SplitPinning H)
    (e : RootPairing.Equiv p.rootDatum q.rootDatum),
    (∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support) →
      ∃! f : SplitPinning.Iso p q,
        (characterLattice.congr f.torusIso).toIntLinearEquiv = e.weightEquiv ∧
        (cocharacterLattice.congr f.torusIso).toIntLinearEquiv =
          e.coweightEquiv.symm ∧
        f.indexEquiv = e.indexEquiv

end Langlands.GroupScheme
