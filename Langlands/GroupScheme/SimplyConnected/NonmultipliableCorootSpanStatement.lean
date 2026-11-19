import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-! # Nonmultipliable relative coroots of a simply connected group span the cocharacters -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Borel–Tits (1972), Proposition 4.3(ii)′ and Corollaire 4.4, lattice form.** Over every
field `k`, let `G` be simply connected and `i : S ⟶ G` a maximal split torus. Let `P` be a root
datum on the actual character and cocharacter lattices of `S`, with the lattice pairing, whose
roots are exactly the nonmultipliable relative roots of `i` (roots `a` of `i` with `2 • a` not a
root), and each of whose reflections is the action of a rational point of `G` normalizing `i`.
Then the integral coroots of `P` span the whole cocharacter lattice of `S`. -/
def NonmultipliableCorootSpanStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSimplyConnected G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
      haveI := hG.isSemisimple.isConnectedReductive.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice S) (cocharacterLattice S)),
        P.toLinearMap = latticePairing S →
        Set.range P.root = {a | a ∈ roots i ∧ (2 : ℤ) • a ∉ roots i} →
        (∀ α : J, ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : S ≅ S),
          IsNormalizingPoint i n σ ∧ characterAut σ = P.reflection α) →
        P.corootSpan ℤ = ⊤

end Langlands.GroupScheme
