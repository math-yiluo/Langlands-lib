import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationStatement

/-! # Exact absolute generation for a nonmultipliable relative root -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- If `a` is a relative root and `2 • a` is absent, the base change of its
relative root group is the smallest closed subgroup containing the absolute
root groups whose roots restrict exactly to `a`. -/
def RelativeRootGroupExactGenerationStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G) (f : S ⟶ T),
      IsMaximalTorus j → CommGroupScheme.groupHom f ≫ j = i →
      IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k K)).obj T.toGrp) →
      letI := hG.isAffineHom
      letI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
        change IsAffineHom (pullback.snd G.X.hom _)
        infer_instance
      ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i →
        let b := algebraBaseMap k K
        let jK := (GroupScheme.baseChange b).map j
        let fK := (CommGroupScheme.baseChange b).map f
        let aK := characterLattice.baseChange b S a
        let F := (RelativeRoot.subgroup i a).baseChange b
        (∀ β ∈ roots jK, fK ≫ β = aK → RelativeRoot.subgroup jK β ≤ F) ∧
        ∀ (H : GroupScheme (Spec (CommRingCat.of K)))
          (h : H ⟶ (GroupScheme.baseChange b).obj G), IsClosedSubgroup h →
          (∀ β ∈ roots jK, fK ≫ β = aK → RelativeRoot.subgroup jK β ≤ SubgroupFunctor.range h) →
          F ≤ SubgroupFunctor.range h

end Langlands.GroupScheme
