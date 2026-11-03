import Langlands.GroupScheme.Absolute.RankOneSolvableReduction
import Langlands.GroupScheme.Reductive.RankOneBorelDynamicStatement
import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Dynamic.WeightExclusion
import Langlands.GroupScheme.Lie.WeightImagePullback

/-! # The exact centralizer-intersection reduction for opposite Lie weights -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every actual intersection with the centralizer of a cocharacter of the
specified torus is a Borel subgroup of that centralizer. This is a property,
not an assertion that such intersections are Borel. -/
def HasBorelCentralizerIntersections
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G) : Prop :=
  ∀ ζ : cocharacterLattice T, IsBorelSubgroup
    (subgroupIntersectionFst
      (Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ j)) b)

variable [IsAlgClosed k]

/-- The two-dynamic-Borel classification excludes opposite Lie-image weights
in the pairwise-dependent root case. The classification is an explicit premise. -/
theorem not_meets_oppositeWeightSpaces_of_rankOneBorelDynamic
    (hrank : RankOneBorelDynamicStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots j, ∀ β ∈ roots j, ¬ LinearIndependent ℤ ![α, β])
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
    (t : T.toGrp ⟶ B) (hb : IsBorelSubgroup b) (ht : t ≫ b = j) :
    haveI := hG.isAffineHom
    ∀ α ∈ roots j, ¬ (Lie.MeetsWeightSpace j b α ∧ Lie.MeetsWeightSpace j b (-α)) := by
  have := hG.isAffineHom
  have := hG.smooth
  intro α hα
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos hα.1
  have hαν : latticePairing T α ν ≠ 0 := by
    rw [hν]
    exact Int.natCast_ne_zero.mpr hD.ne'
  rcases hrank k G hG T j hT hj hdep α hα ν hαν B b t hb ht with hP | hP
  · exact not_meets_oppositeWeightSpaces_of_range_le_parabolic hT j ν b
      hP.2.le α hαν
  · have hαν' : latticePairing T α (-ν) ≠ 0 := by
      simpa only [map_neg, neg_ne_zero] using hαν
    exact not_meets_oppositeWeightSpaces_of_range_le_parabolic hT j (-ν) b
      hP.2.le α hαν'

/-- Over an algebraically closed field, the Borel case of opposite-weight
exclusion follows from connected reductivity of dynamic centralizers, the
rank-one Borel classification, and Borelness of the actual intersections.
All three geometric inputs remain explicit. -/
theorem not_meets_oppositeWeightSpaces_of_borel_centralizers
    (hrank : RankOneBorelDynamicStatement.{u})
    (hcent : DynamicCentralizerReductiveStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
    (t : T.toGrp ⟶ B) (_hb : IsBorelSubgroup b) (ht : t ≫ b = j)
    (hinter : haveI := hG.isAffineHom
      haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      HasBorelCentralizerIntersections j b) :
    haveI := hG.isAffineHom
    ∀ α ∈ roots j, ¬ (Lie.MeetsWeightSpace j b α ∧ Lie.MeetsWeightSpace j b (-α)) := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro α hα
  obtain ⟨ζ, hαζ, hζ⟩ := RootReducedness.exists_cocharacter_pairing_eq_zero
    hT hα.1 (hT.finite_relativeRoots j)
  let m := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ j)
  have hm := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom ζ ≫ j)
  have hmc := Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom ζ ≫ j)
  have hM := hcent k G hG _ _ m hmc hm
  have := hM.isAffineHom
  have : Mono m.hom.hom := hm.1
  let jM := Dynamic.torusFactor j (CommGroupScheme.groupHom ζ) hm
  have hjM : jM ≫ m = j := Dynamic.torusFactor_comp j _ hm
  have hmax : IsMaximalTorus jM := IsMaximalTorus.of_comp hmc (by rwa [hjM])
  have hdep : ∀ β ∈ roots jM, ∀ gamma ∈ roots jM, ¬ LinearIndependent ℤ ![β, gamma] := by
    intro β hβ gamma hgamma
    obtain ⟨hβ', hβζ⟩ := RootReducedness.mem_roots_of_mem_roots_torusFactor j ζ hm hβ
    obtain ⟨hgamma', hgammaζ⟩ := RootReducedness.mem_roots_of_mem_roots_torusFactor j ζ hm hgamma
    exact RootReducedness.not_linearIndependent_of_not_linearIndependent hT hα.1 hgamma'.1
      (hζ β hβ' hβζ) (hζ gamma hgamma' hgammaζ)
  let tI : T.toGrp ⟶ subgroupIntersection m b :=
    pullback.lift jM t (hjM.trans ht.symm)
  have htI : tI ≫ subgroupIntersectionFst m b = jM := pullback.lift_fst _ _ _
  have hroot : α ∈ roots jM := RootReducedness.mem_roots_torusFactor j ζ hm hα hαζ
  have hexclude := not_meets_oppositeWeightSpaces_of_rankOneBorelDynamic hrank
    _ hM T jM hT hmax hdep _ (subgroupIntersectionFst m b) tI (hinter ζ) htI α hroot
  have htransport (β : characterLattice T) (hβζ : latticePairing T β ζ = 0)
      (hβ : Lie.MeetsWeightSpace j b β) :
      Lie.MeetsWeightSpace jM (subgroupIntersectionFst m b) β := by
    apply (Lie.weightSpace_lieImage_comp_iff m jM (subgroupIntersectionFst m b) β).mp
    rw [hjM]
    obtain ⟨X, hX, hX0, Y, hY⟩ := hβ
    obtain ⟨Z, hZ⟩ := RootReducedness.weightSpace_le_range_centralizer j ζ hm hβζ hX
    refine ⟨X, hX, hX0, ?_⟩
    change ∃ W : lieKernel (subgroupIntersection m b) k,
      W.val ≫ (subgroupIntersectionHom m b).hom.hom = X.toMul.val
    apply (Lie.lieImage_subgroupIntersection_iff m b k X.toMul).mpr
    exact ⟨⟨Z.toMul, congrArg (fun V => V.toMul.val) hZ⟩, ⟨Y, hY⟩⟩
  rintro ⟨hpos, hneg⟩
  apply hexclude
  exact ⟨htransport α hαζ hpos, htransport (-α) (by
    simp only [map_neg, LinearMap.neg_apply, hαζ, neg_zero]) hneg⟩

end Langlands.GroupScheme
