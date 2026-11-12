import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.ParabolicIntersection

/-! # Actual intersections of standard parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

/-- A smooth closed overgroup of an actual parabolic is parabolic. -/
theorem IsParabolicSubgroup.of_smooth_overgroup
    {G P H : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {j : H ⟶ G} (hp : IsParabolicSubgroup p)
    (hj : IsClosedSubgroup j) [Smooth H.X.hom]
    (hle : SubgroupFunctor.range p ≤ SubgroupFunctor.range j) :
    IsParabolicSubgroup j := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  let f : P ⟶ H := SubgroupFunctor.factorOfRangeLE hle
  have hf : f ≫ j = p := SubgroupFunctor.factorOfRangeLE_comp hle
  refine ⟨hj, inferInstance, ?_⟩
  obtain ⟨B, b, a, hb, ha⟩ := hp.exists_isBorelSubgroup
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  refine ⟨B, b, a ≫ F.map f, hb, ?_⟩
  rw [Category.assoc, ← F.map_comp, hf]
  exact ha

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Two parabolics from the same standard family intersect in the standard
parabolic indexed by the intersection of their simple-root subsets.
The equality holds on every test scheme. -/
theorem standardParabolic_inter
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν) :
    standardParabolic i ν (J ∩ K) =
      standardParabolic i ν J ⊓ standardParabolic i ν K := by
  let : Smooth G.X.hom := hG.smooth
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hstd := standardCocharacter k G hG T i hi ν hν
  have hord := (standardParabolicOrder k G hG T i hi ν hν).1
  obtain ⟨ζ, hζ⟩ := (hstd J hJ).1
  obtain ⟨eta, heta⟩ := (hstd K hK).1
  have hζP := ((hstd J hJ).2 ζ hζ).1
  have hetaP := ((hstd K hK).2 eta heta).1
  let pJ := Standard.parabolicHom i ν J
  let pK := Standard.parabolicHom i ν K
  let H := subgroupIntersection pJ pK
  let j : H ⟶ G := subgroupIntersectionHom pJ pK
  have hcJ : IsClosedSubgroup pJ := Standard.isClosedSubgroup_parabolicHom i ν J
  have hcK : IsClosedSubgroup pK := Standard.isClosedSubgroup_parabolicHom i ν K
  have hj : IsClosedSubgroup j := isClosedSubgroup_subgroupIntersectionHom hcJ hcK
  have hrep : (standardParabolic i ν J ⊓ standardParabolic i ν K).IsRepresentedBy j := by
    have h := isRepresentedBy_subgroupIntersectionHom hcJ hcK
    rw [(Standard.isRepresentedBy_parabolicHom i ν J).2,
      (Standard.isRepresentedBy_parabolicHom i ν K).2] at h
    exact h
  have hrepD : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy j := by
    rwa [hζP, hetaP] at hrep
  have hetale : SubgroupFunctor.range (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) :=
    (SubgroupFunctor.range_comp_le _ i).trans (range_le_parabolic_groupHom_comp i ζ)
  have : Smooth H.X.hom :=
    (smooth_connected_of_isRepresentedBy_parabolic_inf dynamicConnected _ _ hetale hrepD).1
  let p₀ := Standard.parabolicHom i ν ∅
  have hc₀ : IsClosedSubgroup p₀ := Standard.isClosedSubgroup_parabolicHom i ν ∅
  have hr₀ : SubgroupFunctor.range p₀ =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    (Standard.isRepresentedBy_parabolicHom i ν ∅).2.trans
      (standardParabolicEndpoints k G hG T i hi ν hν).1
  have hp₀ : IsParabolicSubgroup p₀ :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG p₀ hc₀ _ hr₀
  have h₀j : SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range j := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2, hrep.2]
    intro U x hx
    exact ⟨((hord ∅ J (Set.empty_subset _) hJ).1.mp (Set.empty_subset _)) U hx,
      ((hord ∅ K (Set.empty_subset _) hK).1.mp (Set.empty_subset _)) U hx⟩
  have hpj : IsParabolicSubgroup j := hp₀.of_smooth_overgroup hj h₀j
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG H j hj).mp hpj
  have h₀χ : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      Dynamic.parabolic χ := by
    rw [← hr₀, ← hχ]
    exact h₀j
  obtain ⟨I, hI, heI⟩ :=
    (standardParabolicClassification k G hG T i hi ν hν).1 χ h₀χ
  have hinter : standardParabolic i ν J ⊓ standardParabolic i ν K =
      standardParabolic i ν I := hrep.2.symm.trans (hχ.trans heI)
  have hIJ : I ⊆ J :=
    (hord I J hI hJ).1.mpr (by rw [← hinter]; exact fun _ _ hx => hx.1)
  have hIK : I ⊆ K :=
    (hord I K hI hK).1.mpr (by rw [← hinter]; exact fun _ _ hx => hx.2)
  have hJK : J ∩ K ⊆ simpleRelativeRoots i ν := (Set.inter_subset_left).trans hJ
  have hle : standardParabolic i ν (J ∩ K) ≤ standardParabolic i ν I := by
    rw [← hinter]
    intro U x hx
    exact ⟨((hord (J ∩ K) J hJK hJ).1.mp Set.inter_subset_left) U hx,
      ((hord (J ∩ K) K hJK hK).1.mp Set.inter_subset_right) U hx⟩
  have heq : I = J ∩ K :=
    Set.Subset.antisymm (Set.subset_inter hIJ hIK) ((hord (J ∩ K) I hJK hI).1.mpr hle)
  rw [hinter, heq]

namespace Standard

/-- The canonical standard model of the intersected index is the actual
scheme-theoretic intersection of the two supplied canonical standard models. -/
def parabolicInterIso
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν) :
    parabolicScheme i ν (J ∩ K) ≅
      subgroupIntersection (parabolicHom i ν J) (parabolicHom i ν K) := by
  have hrep : (standardParabolic i ν (J ∩ K)).IsRepresentedBy
      (subgroupIntersectionHom (parabolicHom i ν J) (parabolicHom i ν K)) := by
    rw [standardParabolic_inter i ν hG hi hν J K hJ hK]
    have h := isRepresentedBy_subgroupIntersectionHom
      (isClosedSubgroup_parabolicHom i ν J) (isClosedSubgroup_parabolicHom i ν K)
    rwa [(isRepresentedBy_parabolicHom i ν J).2,
      (isRepresentedBy_parabolicHom i ν K).2] at h
  exact (isRepresentedBy_parabolicHom i ν (J ∩ K)).isoOfIsRepresentedBy hrep

@[reassoc (attr := simp)]
theorem parabolicInterIso_hom_comp
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν) :
    (parabolicInterIso i ν hG hi hν J K hJ hK).hom ≫
      subgroupIntersectionHom (parabolicHom i ν J) (parabolicHom i ν K) =
        parabolicHom i ν (J ∩ K) := by
  apply SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp

end Standard

end Langlands.GroupScheme
