import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Rational.SplitTorus

/-! # The relative Weyl group as restrictions of absolute Weyl elements: statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The relative Weyl group is the restriction of the Weyl elements normalizing `S`**
(Borel–Tits, *Groupes réductifs* (1965), Corollaire 5.5). Let `G` be a connected reductive
group over a field `k`, let `i : S ⟶ G` be a maximal split torus, let `K` be an extension
field of `k`, and let `j : T ⟶ G_K` be a maximal `K`-split torus of `G_K` containing `S_K`
through `f : S_K ⟶ T`. Then:

1. every `K`-point of `G_K` normalizing `S_K` is a product `m * z` of a `K`-point `m`
   normalizing both `S_K` and `T` and a `K`-point `z` centralizing `S_K`;
2. the base changes of the automorphisms of `S` induced by the `k`-points of `G` normalizing
   `S` are exactly the automorphisms of `S_K` induced by the `K`-points of `G_K` normalizing
   `T` and `S_K`;
3. a `k`-point normalizing `S` through an automorphism whose base change is the identity
   centralizes `S`. -/
def RelativeWeylAbsoluteRestrictionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of K)))
      (j : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      (f : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S ⟶ T),
      IsMaximalSplitTorus j →
      CommGroupScheme.groupHom f ≫ j = (GroupScheme.baseChange (algebraBaseMap k K)).map i →
      (∀ n ∈ normalizerPoints (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
            ((GroupScheme.baseChange (algebraBaseMap k K)).map i),
        ∃ m ∈ normalizerPoints (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
              ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ⊓ normalizerPoints j,
          ∃ z ∈ centralizerPoints (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
              ((GroupScheme.baseChange (algebraBaseMap k K)).map i),
            n = m * z) ∧
      {τ : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S ≅
          (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S |
        ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : S ≅ S),
          IsNormalizingPoint i n σ ∧
            (CommGroupScheme.baseChange (algebraBaseMap k K)).mapIso σ = τ} =
        {τ | ∃ m ∈ normalizerPoints j,
          IsNormalizingPoint ((GroupScheme.baseChange (algebraBaseMap k K)).map i) m τ} ∧
      ∀ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : S ≅ S),
        IsNormalizingPoint i n σ →
          (CommGroupScheme.baseChange (algebraBaseMap k K)).mapIso σ = Iso.refl _ →
            n ∈ centralizerPoints i

end Langlands.GroupScheme
