import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Rationality of the Weyl group of a split maximal torus: statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The Weyl group of a split maximal torus is rational** (Milne, *Algebraic Groups* (2017),
Proposition 21.1). Let `G` be a connected reductive group over a field `k`, let
`i : T.toGrp ⟶ G` be a maximal torus with `T` split, and let `K` be an extension field of `k`.
Every automorphism of the base-changed torus `T_K` that is induced by conjugation by a
`K`-point of `G_K` normalizing `T_K` is the base change of an automorphism of `T` induced by
conjugation by a `k`-point of `G` normalizing `T`. -/
def SplitMaximalTorusWeylRationalityStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (_ : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G), IsMaximalTorus i →
      ∀ (n' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
          ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X)
        (σ' : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
          (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T),
        IsNormalizingPoint ((GroupScheme.baseChange (algebraBaseMap k K)).map i) n' σ' →
          ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : T ≅ T),
            IsNormalizingPoint i n σ ∧
              (CommGroupScheme.baseChange (algebraBaseMap k K)).mapIso σ = σ'

end Langlands.GroupScheme
