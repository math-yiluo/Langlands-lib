import Langlands.GroupScheme.Reductive.PinnedAutomorphismLift
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.AutomorphicActionPointIso

/-! # Statement: the automorphism group of a pinned split reductive field group -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Automorphisms of a pinned split reductive group** (Conrad, *Reductive group
schemes* (2014), Proposition 7.1.6). Let `G` be a pinned split connected reductive
group over a field `k` and `q : G ⟶ A` an adjoint quotient `A = G/Z_G`. The inner
action of `A(k)` on `G` is an injective group homomorphism `A(k) → Aut G`, and there is
a group homomorphism `Aut G → Aut(R(G, T), Δ)` whose kernel is its image and which is
split by the pinned lift of based root-datum automorphisms. -/
def PinnedAutomorphismGroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G A : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (p : SplitPinning G) (q : G ⟶ A) (hq : IsAdjointQuotient q),
    ∃ (inn : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) →* CategoryTheory.Aut G)
      (π : CategoryTheory.Aut G →* p.basedRootDatumAut),
      (∀ x, inn x = hq.innerAction.basePointIso x) ∧
      Function.Injective inn ∧
      π.ker = inn.range ∧
      ∀ θ, π (p.basedRootDatumAutLift θ) = θ

end Langlands.GroupScheme
