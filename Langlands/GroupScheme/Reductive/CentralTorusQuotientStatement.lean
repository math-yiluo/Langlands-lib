import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Statement: the central quotient of a split reductive group by the kernel of a torus isogeny -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Central torus quotient** (derived from Milne Propositions 21.7, 21.8 and 17.20 and
Theorem 5.14). Let `i : T ⟶ G` be a split maximal torus of a connected reductive group over a
field, and let `t : T ⟶ T'` be a homomorphism to a split torus whose character map
`χ ↦ t ≫ χ` and cocharacter map `ν ↦ ν ≫ t` are injective, so that `t` is an isogeny of tori.
If every root of `i` is of the form `t ≫ α'`, then there are a connected reductive group `Q`, a
central isogeny `q : G ⟶ Q` and a maximal torus `i'' : T' ⟶ Q` with `i ≫ q = t ≫ i''`. -/
def SplitCentralTorusQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    ∀ i : T.toGrp ⟶ G, IsMaximalTorus i → ∀ t : T ⟶ T',
      Function.Injective (fun χ : characterLattice T' => t ≫ χ) →
      Function.Injective (fun ν : cocharacterLattice T => ν ≫ t) →
      (haveI := hG.isAffineHom; ∀ α ∈ roots i, ∃ α' : characterLattice T', α = t ≫ α') →
        ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive Q)
          (q : G ⟶ Q) (i'' : T'.toGrp ⟶ Q),
          IsMaximalTorus i'' ∧ IsCentralIsogeny q ∧ i ≫ q = CommGroupScheme.groupHom t ≫ i''

end Langlands.GroupScheme
