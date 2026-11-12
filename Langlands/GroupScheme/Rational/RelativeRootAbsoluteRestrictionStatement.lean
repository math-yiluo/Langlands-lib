import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Relative roots as restrictions of absolute roots: statement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The relative roots are the nonzero restrictions of the absolute roots** (Milne,
*Algebraic Groups* (2017), 25.19 and footnote 2 to 25.13). Let `G` be a connected reductive
group over a field `k`, let `i : S ⟶ G` be a maximal split torus, and let `j : T ⟶ G` be a
maximal torus containing `S` through `f : S ⟶ T`. Let `K` be an extension field of `k` over
which `T` splits. Then a character `α` of `S` is a relative root of `(G, S)` if and only if
`α ≠ 0` and the base change of `α` to `K` is the restriction to `S_K` of a root of
`(G_K, T_K)`. -/
def RelativeRootAbsoluteRestrictionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G) (f : S ⟶ T),
      IsMaximalTorus j → CommGroupScheme.groupHom f ≫ j = i →
      IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k K)).obj T.toGrp) →
      haveI := hG.isAffineHom
      haveI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
        change IsAffineHom (pullback.snd G.X.hom _)
        infer_instance
      ∀ α : characterLattice S,
        α ∈ relativeRoots i ↔
          α ≠ 0 ∧ ∃ β ∈ roots ((GroupScheme.baseChange (algebraBaseMap k K)).map j),
            (CommGroupScheme.baseChange (algebraBaseMap k K)).map f ≫ β =
              characterLattice.baseChange (algebraBaseMap k K) S α

end Langlands.GroupScheme
