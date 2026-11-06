import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: the roots of the centralizer of a cocharacter of a split maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Roots of the centralizer of a cocharacter** (Milne Theorem 13.33(c) and Proposition
21.90(a); Conrad–Gabber–Prasad Proposition 2.1.8(1)). Let `i : T ⟶ G` be a split maximal
torus of a connected reductive group over a field, let `ν` be a cocharacter of `T`, and let
`z : Z ⟶ G` be a closed subgroup representing the dynamic centralizer `Z_G(ν)` of
`ν ≫ i`. Suppose that `Z` is connected reductive and that `t : T ⟶ Z` satisfies
`t ≫ z = i`. Then the roots of `t` are the roots `α` of `i` with `⟨α, ν⟩ = 0`. -/
def DynamicCentralizerRootsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
    ∀ (ν : cocharacterLattice T) (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
      IsClosedSubgroup z →
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy z →
      ∀ (hZ : IsConnectedReductive Z) (t : T.toGrp ⟶ Z), t ≫ z = i →
        haveI := hG.isAffineHom
        haveI := hZ.isAffineHom
        roots t = {α | α ∈ roots i ∧ latticePairing T α ν = 0}

end Langlands.GroupScheme
