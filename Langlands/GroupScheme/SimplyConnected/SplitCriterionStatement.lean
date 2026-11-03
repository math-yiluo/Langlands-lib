import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-! # Coroot generation of the cocharacter lattice implies simple connectedness -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Coroot criterion, sufficiency** (Milne, Proposition 23.29; the "if" direction of the
criterion quoted from Conrad–Gabber–Prasad, Theorem A.4.10, in the proof of Corollary A.4.11).
Over every field `k`, let `G` be semisimple, let `i : T ⟶ G` be a maximal torus with `T` split,
and let `P` be a root datum of `i` on the actual character and cocharacter lattices of `T`. If
the integral coroots of `P` span the whole cocharacter lattice, then `G` is simply connected. -/
def SplitCorootSpanSimplyConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsSemisimple G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus T.toGrp →
    ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isConnectedReductive.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → P.corootSpan ℤ = ⊤ → IsSimplyConnected G

end Langlands.GroupScheme
