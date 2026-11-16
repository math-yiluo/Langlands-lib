import Langlands.GroupScheme.Rational.NonnegativeRootParabolicGeneration
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.Rational.LocalRootGeneration
import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements

/-! # All-test generation of dynamic centralizers and radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- Closed generation by the whole-torus centralizer and the zero roots,
on every test scheme, with no smoothness assumption on the competitor. -/
theorem dynamicCentralizer_le_of_zeroRootSubgroups_le
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ζ : cocharacterLattice T) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcent : torusCentralizer i ≤ SubgroupFunctor.range d)
    (hroot : ∀ a ∈ relativeRoots i, latticePairing T a ζ = 0 →
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range d) :
    Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) ≤
      SubgroupFunctor.range d := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let M := Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom ζ ≫ i)
  let j : M ⟶ G := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom _
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom _
  have hM : IsConnectedReductive M := dynamicCentralizerReductive k G hG _ M j hjc hj
  let : IsAffineHom M.X.hom := hjc.isAffineHom
  let : Smooth M.X.hom := hM.smooth
  let : ConnectedSpace M.X.left := hM.connectedSpace
  let iM := Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj
  have hcomp : iM ≫ j = i := Dynamic.torusFactor_comp i _ hj
  have hiM : IsMaximalSplitTorus iM :=
    IsMaximalSplitTorus.of_comp hjc (hcomp.symm ▸ hi)
  let q := subgroupIntersectionFst j d
  have hq : IsClosedSubgroup q := isClosedSubgroup_subgroupIntersectionFst j hd
  have hinto : (SubgroupFunctor.range d).comap j ≤ SubgroupFunctor.range q := by
    intro U x hx
    change ∃ y : U ⟶ D.X, y ≫ d.hom.hom = x ≫ j.hom.hom at hx
    obtain ⟨y, hy⟩ := hx
    let hpb := subgroupIntersection_isPullback j d
    change ∃ z : U ⟶ (subgroupIntersection j d).X, z ≫ q.hom.hom = x
    exact ⟨hpb.lift x y hy.symm, hpb.lift_fst _ _ _⟩
  have hcentM : torusCentralizer iM ≤ SubgroupFunctor.range q := by
    apply le_trans ?_ hinto
    intro U x hx
    apply hcent U
    intro V b t
    apply (commute_iff_eq _ _).mpr
    change (b ≫ x ≫ j.hom.hom) * (t ≫ i.hom.hom) =
      (t ≫ i.hom.hom) * (b ≫ x ≫ j.hom.hom)
    have he := congrArg (fun f => f ≫ j.hom.hom) (hx V b t).eq
    simpa only [← hcomp, Grp.comp_hom_hom, MonObj.mul_comp, Category.assoc] using he
  have hrootM : ∀ a ∈ relativeRoots iM, 0 ≤ latticePairing T a ζ →
      RelativeRoot.subgroup iM a ≤ SubgroupFunctor.range q := by
    intro a ha _
    apply le_trans ?_ hinto
    intro U x hx
    apply hroot a (relativeRoots_subset_of_factor hj iM hcomp ha)
      (relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hj iM hcomp ζ le_rfl ha) U
    have hm := RelativeRoot.comp_mem_subgroup iM a j hx
    rwa [hcomp] at hm
  have htop : Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ iM) = ⊤ := by
    apply Dynamic.parabolic_eq_top_of_centralizer
    apply (isCentral_iff_dynamicCentralizer_eq_top _).mp
    exact (isCentral_comp_iff_le_dynamicCentralizer hj iM hcomp ζ).mpr le_rfl
  have hfull := RelativeRoot.dynamicParabolic_le_of_nonnegative_rootSubgroups_le
    iM hiM.isSplitSubtorus ζ q hq hcentM hrootM
  rw [htop] at hfull
  intro U x hx
  obtain ⟨m, rfl⟩ := SubgroupFunctor.mem_range.mp (hj.2.symm ▸ hx)
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hfull U (Subgroup.mem_top m))
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y ≫ (subgroupIntersectionSnd j d).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, ← subgroupIntersection_condition]
  change y ≫ q.hom.hom ≫ j.hom.hom = m ≫ j.hom.hom
  rw [← Category.assoc, hy]

namespace RelativeRoot

/-- A generic cocharacter supplies a positive integral ray from an indivisible
root through every actual relative root. -/
theorem exists_indivisibleRoot_multiple (i : T.toGrp ⟶ G)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    ∃ b ∈ indivisibleRoots i, ∃ n : ℕ, 0 < n ∧ n • b = a := by
  obtain ⟨eta, heta⟩ : ∃ eta : cocharacterLattice T, 0 < latticePairing T a eta := by
    by_cases hp : 0 < latticePairing T a ν
    · exact ⟨ν, hp⟩
    · refine ⟨-ν, ?_⟩
      have hn := hν a ha
      simp only [map_neg]
      omega
  obtain ⟨b, hb, n, _, hn, hna⟩ := exists_indivisiblePositiveRoot_ray i eta ha heta
  exact ⟨b, hb.1, n, hn, hna⟩

/-- A condition stable under division by positive natural multiples lets either
allowed ambient root set supply all required root subgroup containments. -/
theorem subgroup_le_of_ambient_pred
    (i : T.toGrp ⟶ G) {R : Set (characterLattice T)}
    (hR : IsRelativeRootAmbient i R)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (p : characterLattice T → Prop)
    (hdiv : ∀ b (n : ℕ), 0 < n → p (n • b) → p b)
    {F : SubgroupFunctor G}
    (hF : ∀ b ∈ R, p b → subgroup i b ≤ F)
    {a : characterLattice T} (ha : a ∈ relativeRoots i) (hpa : p a) :
    subgroup i a ≤ F := by
  rcases hR with rfl | rfl
  · exact hF a ha hpa
  · obtain ⟨b, hb, n, hn, rfl⟩ := exists_indivisibleRoot_multiple i hν ha
    exact (subgroup_nsmul_le i b hn).trans (hF b hb (hdiv b n hn hpa))

/-- The complete dynamic radical lies in every subgroup functor containing
its indivisible positive root functors. The competitor need not be closed. -/
theorem dynamicUnipotent_le_of_indivisiblePositiveRoots_le
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ζ : cocharacterLattice T) (F : SubgroupFunctor G)
    (hroot : ∀ a ∈ indivisiblePositiveRoots i ζ, subgroup i a ≤ F) :
    Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i) ≤ F := by
  classical
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨n, a, hinj, ha⟩ := exists_fin_enumeration_indivisiblePositiveRoots i ζ
    (hi.isSplitSubtorus.1.finite_relativeRoots i)
  obtain ⟨U, jU, H, j, e, hjU, _, _, _, _, _, hj, he⟩ :=
    dynamicRootOrderedProduct k G hG T i hi ζ n a hinj ha
  intro V x hx
  have hx' : x ∈ (SubgroupFunctor.range jU).carrier V := hjU.2.symm ▸ hx
  have hfactor (r : Fin n) : (SubgroupFunctor.range (j r)).carrier V ≤ F.carrier V := by
    rw [(hj r).1.2]
    exact hroot (a r) (ha ▸ Set.mem_range_self r) V
  have hle := range_le_of_orderedProductIso j jU e he V (F.carrier V) hfactor
  exact hle hx'

end RelativeRoot

end Langlands.GroupScheme
