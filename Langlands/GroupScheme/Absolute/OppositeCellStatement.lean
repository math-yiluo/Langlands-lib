import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice

/-! # The opposite open cell for a smooth affine group over a field: statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The opposite open cell** (Conrad–Gabber–Prasad, Proposition 2.1.8(3); Conrad, Theorem
4.1.7(4)). Let `G` be a smooth affine group scheme over a field, `χ : 𝔾_m ⟶ G` a cocharacter and
`χ⁻¹` the composite of `χ` with the inversion `t ↦ t⁻¹` of `𝔾_m`. If `iU : U ⟶ G` represents
`U(χ⁻¹)` and `iP : P ⟶ G` represents `P(χ)`, then the multiplication morphism
`U ×_S P ⟶ G`, `(u, p) ↦ u p`, is an open immersion. -/
def OppositeCellStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U P : GroupScheme (Spec (CommRingCat.of k))) (iU : U ⟶ G) (iP : P ⟶ G),
    (Dynamic.unipotent
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy
      iU →
    (Dynamic.parabolic χ).IsRepresentedBy iP →
      IsOpenImmersion ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)).left

end Langlands.GroupScheme
