import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.IdentityComponent

/-! # Centralizers of multiplicative-type groups in connected reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Centralizers of groups of multiplicative type** (Conrad, *Reductive group schemes*,
Remark 3.1.5 over a field; Conrad–Gabber–Prasad, Propositions A.8.10(2) and A.8.12). Let `G`
be a connected reductive group over a field `k`, `H` a commutative group scheme of
multiplicative type and `i : H ⟶ G` a homomorphism. Every closed subgroup `j : C ⟶ G`
representing the all-test centralizer of `i` is smooth, and its identity component is
connected reductive. -/
def MultiplicativeTypeCentralizerReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (H : CommGroupScheme (Spec (CommRingCat.of k))) (i : H.toGrp ⟶ G),
    IsMultiplicativeType H.toGrp →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
      (torusCentralizer i).IsRepresentedBy j → ∀ hclosed : IsClosedSubgroup j,
      ∃ hC : Smooth C.X.hom,
        letI : Smooth C.X.hom := hC
        letI : IsAffineHom G.X.hom := hG.isAffineHom
        letI : IsClosedImmersion j.hom.hom.left := hclosed
        letI : IsAffineHom C.X.hom := by
          have h : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
          simpa only [Over.w] using h
        IsConnectedReductive (identityComponent C)

end Langlands.GroupScheme
