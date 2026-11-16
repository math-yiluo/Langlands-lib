import Langlands.GroupScheme.Rational.StandardRootSubsetGeneration
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection

/-! # The group ranges attached to standard root subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- The weak pairing locus generates the dynamic parabolic, with either
the full or indivisible ambient roots. -/
theorem IsRootSubsetGroup.range_eq_dynamicParabolic
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {R : Set (characterLattice T)} (hR : IsRelativeRootAmbient i R)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (ζ : cocharacterLattice T) {h : H ⟶ G}
    (hh : IsRootSubsetGroup i {a | a ∈ R ∧ 0 ≤ latticePairing T a ζ} h) :
    SubgroupFunctor.range h = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hsub : R ⊆ relativeRoots i := by
    rcases hR with rfl | rfl
    · exact subset_rfl
    · exact fun _ ha => ha.1
  apply le_antisymm
  · let P := Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ζ ≫ i)
    let j : P ⟶ G := Dynamic.Affine.parabolicHom _
    have hj := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ζ ≫ i)
    rw [← hj.2]
    apply hh.2.2.2 P j (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
    · rw [hj.2]
      exact (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ)).trans
        (Dynamic.centralizer_le_parabolic _)
    · intro a ha
      rw [hj.2]
      exact RelativeRoot.subgroup_le_dynamicParabolic_of_nonneg i hi.isSplitSubtorus ζ a
        (hsub ha.1).1 ha.2
  · apply RelativeRoot.dynamicParabolic_le_of_nonnegative_rootSubgroups_le
      i hi.isSplitSubtorus ζ h hh.1 hh.2.1
    intro a ha hpair
    apply RelativeRoot.subgroup_le_of_ambient_pred i hR hν
      (fun b => 0 ≤ latticePairing T b ζ) ?_ (fun b hb hp => hh.2.2.1 b ⟨hb, hp⟩)
      ha hpair
    intro b n hn hp
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hp
    have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
    nlinarith

/-- The zero pairing locus generates the dynamic centralizer. -/
theorem IsRootSubsetGroup.range_eq_dynamicCentralizer
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {R : Set (characterLattice T)} (hR : IsRelativeRootAmbient i R)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (ζ : cocharacterLattice T) {h : H ⟶ G}
    (hh : IsRootSubsetGroup i {a | a ∈ R ∧ latticePairing T a ζ = 0} h) :
    SubgroupFunctor.range h = Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply le_antisymm
  · let M := Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom ζ ≫ i)
    let j : M ⟶ G := Dynamic.Affine.centralizerHom _
    have hj := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
    rw [← hj.2]
    apply hh.2.2.2 M j (Dynamic.Affine.isClosedSubgroup_centralizerHom _)
    · rw [hj.2]
      exact torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ)
    · intro a ha
      rw [hj.2]
      exact RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i a ζ ha.2
  · apply dynamicCentralizer_le_of_zeroRootSubgroups_le hG i hi ζ h hh.1 hh.2.1
    intro a ha hpair
    apply RelativeRoot.subgroup_le_of_ambient_pred i hR hν
      (fun b => latticePairing T b ζ = 0) ?_ (fun b hb hp => hh.2.2.1 b ⟨hb, hp⟩)
      ha hpair
    intro b n hn hp
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hp
    have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
    nlinarith

/-- The strict pairing locus generates the dynamic unipotent subgroup. -/
theorem IsRootSubsetUnipotentGroup.range_eq_dynamicUnipotent
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {R : Set (characterLattice T)} (hR : IsRelativeRootAmbient i R)
    {ν : cocharacterLattice T} (_hν : IsGenericCocharacter i ν)
    (ζ : cocharacterLattice T) {h : H ⟶ G}
    (hh : IsRootSubsetUnipotentGroup i {a | a ∈ R ∧ 0 < latticePairing T a ζ} h) :
    SubgroupFunctor.range h = Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply le_antisymm
  · let U := Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ζ ≫ i)
    let j : U ⟶ G := Dynamic.Affine.unipotentHom _
    have hj := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom ζ ≫ i)
    rw [← hj.2]
    apply hh.2.2 U j (Dynamic.Affine.isClosedSubgroup_unipotentHom _)
    intro a ha
    rw [hj.2]
    exact RelativeRoot.subgroup_le_dynamicUnipotent i ζ ha.2
  · apply RelativeRoot.dynamicUnipotent_le_of_indivisiblePositiveRoots_le
      hG i hi ζ (SubgroupFunctor.range h)
    intro a ha
    apply hh.2.1 a
    refine ⟨?_, ha.2⟩
    rcases hR with rfl | rfl
    · exact ha.1.1
    · exact ha.1

/-- Negation stability turns the unipotent part of the weak pairing locus
into the strict pairing locus. -/
theorem standardUnipotentRootSubset_eq_of_pairing
    {R Θ : Set (characterLattice T)} {ν ζ : cocharacterLattice T}
    (hneg : ∀ a ∈ R, -a ∈ R)
    (hP : standardParabolicRootSubset R ν Θ =
      {a | a ∈ R ∧ 0 ≤ latticePairing T a ζ}) :
    standardUnipotentRootSubset R ν Θ = {a | a ∈ R ∧ 0 < latticePairing T a ζ} := by
  ext a
  change (a ∈ standardParabolicRootSubset R ν Θ ∧
    -a ∉ standardParabolicRootSubset R ν Θ) ↔ _
  rw [hP]
  constructor
  · intro ha
    refine ⟨ha.1.1, ?_⟩
    have hn : ¬ 0 ≤ -latticePairing T a ζ := by
      intro hn
      apply ha.2
      exact ⟨hneg a ha.1.1, by simpa using hn⟩
    omega
  · rintro ⟨ha, hp⟩
    refine ⟨⟨ha, hp.le⟩, ?_⟩
    intro hn
    have hn' : 0 ≤ -latticePairing T a ζ := by simpa using hn.2
    omega

end Langlands.GroupScheme
