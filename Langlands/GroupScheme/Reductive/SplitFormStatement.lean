import Langlands.GroupScheme.Reductive.SplitClassificationStatement
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.SeparableClosure

/-! # The split form of a reductive group: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The split form** (Milne, *Algebraic Groups* (2017), Corollary 23.57). Let `G` be a
connected reductive group over a field `k` and let `k_s` be a separable closure of `k`.

1. There is a split connected reductive group `G₀` over `k` (one with a split maximal torus)
   such that `G₀` and `G` become isomorphic over `k_s`.
2. `G₀` is unique up to isomorphism: two split connected reductive groups over `k` that both
   become isomorphic to `G` over `k_s` are isomorphic over `k`. -/
def SplitFormStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      (∃ (G₀ : GroupScheme (Spec (CommRingCat.of k)))
          (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (i₀ : T₀.toGrp ⟶ G₀),
        IsConnectedReductive G₀ ∧ IsSplitTorus T₀.toGrp ∧ IsMaximalTorus i₀ ∧
          Nonempty ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G₀ ≅
            (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G)) ∧
      ∀ (G₁ G₂ : GroupScheme (Spec (CommRingCat.of k)))
        (T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of k)))
        (i₁ : T₁.toGrp ⟶ G₁) (i₂ : T₂.toGrp ⟶ G₂),
        IsConnectedReductive G₁ → IsConnectedReductive G₂ →
        IsSplitTorus T₁.toGrp → IsSplitTorus T₂.toGrp →
        IsMaximalTorus i₁ → IsMaximalTorus i₂ →
        Nonempty ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G₁ ≅
          (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G) →
        Nonempty ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G₂ ≅
          (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G) →
        Nonempty (G₁ ≅ G₂)

end Langlands.GroupScheme
