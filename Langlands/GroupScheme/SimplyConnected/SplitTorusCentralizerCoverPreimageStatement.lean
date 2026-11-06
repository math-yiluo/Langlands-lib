import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # The preimage of a split-torus centralizer in a simply connected cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `G` be connected reductive over a field `k`, with derived subgroup `d : D ⟶ G` and a
central isogeny `π : C ⟶ D` from a simply connected group `C`. Let `M = Z_G(A)`, given by
`j : M ⟶ G`, be the centralizer of a split subtorus `a : A ⟶ G`; let `dM : DM ⟶ M` with
`πM : CM ⟶ DM` be a simply connected cover of the derived subgroup of `M`, and `t : T ⟶ M` a
maximal torus. Then the preimage of `M` in `C` is the centralizer `M' = Z_C(A')`, given by
`j' : M' ⟶ C`, of a split subtorus `a' : A' ⟶ C`; `M'` is connected reductive and the
restriction `p : M' ⟶ M` of `π ≫ d` satisfies:
* some positive multiple of every rational character of `M'` is pulled back along `p` from a
  rational character of `M`;
* the derived subgroup `d' : D' ⟶ M'` lifts along `p` to `CM`: `b ≫ πM ≫ dM = d' ≫ p`;
* some maximal torus `t' : T' ⟶ M'` maps into `T`, `t' ≫ p = g ≫ t`, and `T'` splits over
  every field extension of `k` over which `T` splits. -/
def SplitTorusCentralizerCoverPreimageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D C : GroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ G) (π : C ⟶ D),
    IsConnectedReductive G → IsDerivedSubgroup d → IsSimplyConnected C → IsCentralIsogeny π →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G), IsSplitSubtorus a →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer a).IsRepresentedBy j →
    ∀ (DM CM : GroupScheme (Spec (CommRingCat.of k))) (dM : DM ⟶ M) (πM : CM ⟶ DM),
      IsSimplyConnectedDerivedCover dM πM →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ M), IsMaximalTorus t →
    ∃ (A' : CommGroupScheme (Spec (CommRingCat.of k))) (a' : A'.toGrp ⟶ C)
      (M' : GroupScheme (Spec (CommRingCat.of k))) (j' : M' ⟶ C) (p : M' ⟶ M),
      IsSplitSubtorus a' ∧ (torusCentralizer a').IsRepresentedBy j' ∧
      IsConnectedReductive M' ∧
      j' ≫ π ≫ d = p ≫ j ∧
      SubgroupFunctor.range j' = (SubgroupFunctor.range j).comap (π ≫ d) ∧
      (∀ χ' : rationalCharacters M', ∃ n : ℕ, 0 < n ∧
        ∃ χ : rationalCharacters M, n • χ' = characterRestrict p χ) ∧
      (∃ (D' : GroupScheme (Spec (CommRingCat.of k))) (d' : D' ⟶ M') (b : D' ⟶ CM),
        IsDerivedSubgroup d' ∧ b ≫ πM ≫ dM = d' ≫ p) ∧
      (∃ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (t' : T'.toGrp ⟶ M') (g : T' ⟶ T),
        IsMaximalTorus t' ∧ t' ≫ p = CommGroupScheme.groupHom g ≫ t ∧
        ∀ (E : Type u) [Field E] [Algebra k E],
          IsSplitTorus ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj T.toGrp) →
            IsSplitTorus ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj T'.toGrp))

end Langlands.GroupScheme
