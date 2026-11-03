import Langlands.GroupScheme.Dynamic.CentralShifts
import Langlands.GroupScheme.Dynamic.PositiveScaling
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.RootSignParabolicLie

/-! # Minimality of a proper rank-one dynamic parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A nonnegative pairing with every actual relative root forces the dynamic
parabolic to be the whole smooth connected affine group. -/
theorem Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hν : ∀ α ∈ relativeRoots i, 0 ≤ latticePairing T α ν) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) = ⊤ := by
  classical
  have hLie : RelativeRoot.tangentSubmodule
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) = ⊤ := by
    rw [RelativeRoot.tangentSubmodule_parabolic_eq_semigroupWeightSpan hT i ν,
      RelativeRoot.semigroupWeightSpan_conjugation,
      RelativeRoot.adjointSemigroupWeightSpan]
    apply top_unique
    rw [← (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top]
    refine iSup_le fun α => ?_
    by_cases hbot : weightSpace i α = ⊥
    · rw [hbot]
      exact bot_le
    have hα : α ∈ RelativeRoot.nonnegativeSemigroup ν := by
      change 0 ≤ latticePairing T α ν
      by_cases hzero : α = 0
      · simp [hzero]
      · exact hν α ⟨hzero, hbot⟩
    exact le_iSup (fun χ : RelativeRoot.nonnegativeSemigroup ν => weightSpace i χ.val)
      ⟨α, hα⟩
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let P := Dynamic.Affine.parabolicScheme χ
  let j : P ⟶ G := Dynamic.Affine.parabolicHom χ
  have hj : (Dynamic.parabolic χ).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have : Smooth P.X.hom := (dynamicSmooth k G χ P j).1 hj
  have hfull : SubgroupFunctor.range j = ⊤ := by
    apply lieSubgroupEquality k G P j (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
    intro X
    apply hj.exists_lieKernel_lift X
    change Additive.ofMul X ∈ RelativeRoot.tangentSubmodule (Dynamic.parabolic χ)
    rw [hLie]
    exact Submodule.mem_top
  exact hj.2.symm.trans hfull

namespace RelativeRoot

/-- If all actual roots are integral multiples of one character, the integral
cross difference of two cocharacters is central on every scheme test. -/
theorem isCentral_cross_difference_of_cyclic_relativeRoots
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν eta : cocharacterLattice T) :
    IsCentral (CommGroupScheme.groupHom
      ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) ≫ i) := by
  apply rootAnnihilatorCentrality k G T hT i
  intro α hα
  obtain ⟨n, rfl⟩ := hcyclic α hα
  simp only [map_sub, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Two cocharacters pairing positively with the cyclic root direction have
the same actual dynamic parabolic. -/
theorem rankOneParabolic_eq_of_pairings_pos
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν eta : cocharacterLattice T)
    (hν : 0 < latticePairing T a ν) (heta : 0 < latticePairing T a eta) :
    Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hcentral := isCentral_cross_difference_of_cyclic_relativeRoots hT i a hcyclic ν eta
  have hshift := Dynamic.parabolic_add_of_isCentral i
    ((latticePairing T a eta) • ν)
    ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) hcentral
  have hadd : (latticePairing T a eta) • ν +
      ((latticePairing T a ν) • eta - (latticePairing T a eta) • ν) =
        (latticePairing T a ν) • eta := by abel
  rw [hadd, Dynamic.parabolic_zsmul T i eta hν,
    Dynamic.parabolic_zsmul T i ν heta] at hshift
  exact hshift

/-- Containment in a proper rank-one parabolic forces a positive pairing with
its chosen cyclic root direction. -/
theorem pairing_pos_of_rankOneParabolic_le
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν eta : cocharacterLattice T) (hν : 0 < latticePairing T a ν)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    0 < latticePairing T a eta := by
  by_contra hpos
  have heta : latticePairing T a eta ≤ 0 := le_of_not_gt hpos
  apply hproper
  apply Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots hT i ν
  intro α hα
  obtain ⟨n, rfl⟩ := hcyclic α hα
  by_contra hneg
  have hn : n < 0 := by
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at hneg
    nlinarith
  have hnonneg : 0 ≤ latticePairing T (n • a) eta := by
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg_of_nonpos_of_nonpos hn.le heta
  exact hneg (nonnegative_rootSupport_of_parabolic_le hT i eta ν hle (n • a) hα hnonneg)

/-- A proper parabolic in a cyclic actual root system is minimal among the
dynamic parabolics of cocharacters on that same split torus. -/
theorem rankOneParabolic_eq_of_le
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν eta : cocharacterLattice T) (hν : 0 < latticePairing T a ν)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
  rankOneParabolic_eq_of_pairings_pos hT i a hcyclic ν eta hν
    (pairing_pos_of_rankOneParabolic_le hT i a hcyclic ν eta hν hproper hle)

/-- The canonical inclusion-compatible isomorphism of representatives of two
nested dynamic parabolics on a split torus with cyclic actual roots, when the
larger one is proper. -/
def rankOneParabolicIsoOfLE
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν eta : cocharacterLattice T) (hν : 0 < latticePairing T a ν)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))
    {P Q : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ G) (l : Q ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy j)
    (hl : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy l) : P ≅ Q :=
  hj.isoOfIsRepresentedBy
    (by rw [rankOneParabolic_eq_of_le hT i a hcyclic ν eta hν hproper hle]; exact hl)

/-- The rank-one isomorphism respects the actual ambient inclusions. -/
theorem rankOneParabolicIsoOfLE_hom_comp
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (a : characterLattice T)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν eta : cocharacterLattice T) (hν : 0 < latticePairing T a ν)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))
    {P Q : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ G) (l : Q ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy j)
    (hl : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy l) :
    (rankOneParabolicIsoOfLE hT i a hcyclic ν eta hν hproper hle j l hj hl).hom ≫ l = j :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end RelativeRoot
end Langlands.GroupScheme
