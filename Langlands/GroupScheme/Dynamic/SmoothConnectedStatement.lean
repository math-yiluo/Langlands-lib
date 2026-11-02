import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Statements: smoothness and connectedness of dynamic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Smoothness of dynamic subgroups** (Conrad–Gabber–Prasad, Proposition 2.1.8(3)). Let `G`
be a smooth affine group scheme over a field `k` and `χ` a cocharacter of `G`. Every group scheme
`H` with a homomorphism `j : H ⟶ G` representing one of the subgroup functors
`Dynamic.parabolic χ`, `Dynamic.centralizer χ` or `Dynamic.unipotent χ` is smooth over `k`. -/
def DynamicSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    ((Dynamic.parabolic χ).IsRepresentedBy j → Smooth H.X.hom) ∧
    ((Dynamic.centralizer χ).IsRepresentedBy j → Smooth H.X.hom) ∧
    ((Dynamic.unipotent χ).IsRepresentedBy j → Smooth H.X.hom)

/-- **Connectedness of dynamic subgroups** (Conrad–Gabber–Prasad, Proposition 2.1.8(4)). Let `G`
be a smooth affine group scheme over a field `k` and `χ` a cocharacter of `G`. A representative
of `Dynamic.unipotent χ` has connected underlying space; if `G` has connected underlying space,
then so do representatives of `Dynamic.parabolic χ` and `Dynamic.centralizer χ`. -/
def DynamicConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    ((Dynamic.unipotent χ).IsRepresentedBy j → ConnectedSpace H.X.left) ∧
    (ConnectedSpace G.X.left →
      ((Dynamic.parabolic χ).IsRepresentedBy j → ConnectedSpace H.X.left) ∧
      ((Dynamic.centralizer χ).IsRepresentedBy j → ConnectedSpace H.X.left))

end Langlands.GroupScheme
