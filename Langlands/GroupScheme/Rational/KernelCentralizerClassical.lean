import Langlands.GroupScheme.Rational.KernelCentralizerProportionalRoots
import Langlands.GroupScheme.Rational.KernelCentralizerRootReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.IdentityComponent.Transport

/-! # The classical maximal-torus argument for full-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

section Base

variable {B : Scheme.{u}} {S T : CommGroupScheme B} {G M : GroupScheme B}

/-- A commutative overgroup centralizes every character kernel in a torus
mapping to it, on every scheme test. -/
theorem range_le_kernelCentralizer_of_torus_factor
    (f : S ⟶ T) (t : T.toGrp ⟶ G) (a : characterLattice S) :
    SubgroupFunctor.range t ≤ kernelCentralizer (CommGroupScheme.groupHom f ≫ t) a := by
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [mem_kernelCentralizer]
  intro W b c
  apply (commute_iff_eq _ _).mpr
  simpa only [MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun z : W ⟶ T.X => z ≫ t.hom.hom)
      (mul_comm (b ≫ y) (c ≫ (characterKernelι a).hom.hom ≫
        (CommGroupScheme.groupHom f).hom.hom))

/-- A self-centralizing commutative subgroup stays self-centralizing in any
monic intermediate subgroup through which it factors. -/
theorem torusCentralizer_eq_range_of_comp_mono
    (t : T.toGrp ⟶ M) (q : M ⟶ G) [Mono q.hom.hom]
    (hself : torusCentralizer (t ≫ q) = SubgroupFunctor.range (t ≫ q)) :
    torusCentralizer t = SubgroupFunctor.range t := by
  apply le_antisymm _ (range_le_torusCentralizer t)
  intro V x hx
  have hmap : x ≫ q.hom.hom ∈ (torusCentralizer (t ≫ q)).carrier V := by
    intro W b y
    apply (commute_iff_eq _ _).mpr
    simpa only [MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun z : W ⟶ M.X => z ≫ q.hom.hom) (hx W b y).eq
  rw [hself] at hmap
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hmap
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y, (cancel_mono q.hom.hom).mp ?_⟩
  simpa only [Grp.comp_hom_hom, Category.assoc] using hy

end Base

section Field

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (f : S ⟶ T) (t : T.toGrp ⟶ G) (a : characterLattice S)
    (j : C ⟶ G)
    (hj : (kernelCentralizer (CommGroupScheme.groupHom f ≫ t) a).IsRepresentedBy j)

/-- The containing split torus factors canonically through the actual identity
component of any smooth affine full-kernel centralizer representative. -/
def kernelCentralizerTorusFactor (hT : IsSplitTorus T.toGrp) :
    T.toGrp ⟶ identityComponent C := by
  let : ConnectedSpace T.X.left := hT.connectedSpace
  exact IdentityComponent.factor C
    (hj.factorHom t (range_le_kernelCentralizer_of_torus_factor f t a))

@[reassoc (attr := simp)]
theorem kernelCentralizerTorusFactor_comp (hT : IsSplitTorus T.toGrp) :
    kernelCentralizerTorusFactor f t a j hj hT ≫ identityComponentι C ≫ j = t := by
  rw [kernelCentralizerTorusFactor, IdentityComponent.factor_identityComponentι_assoc,
    hj.factorHom_comp]

end Field

/-- Over an algebraically closed field every split-torus homomorphism into an
affine locally finite-type group factors through a split maximal torus. -/
theorem exists_factor_split_maximalTorus
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
      (f : S ⟶ T), IsSplitTorus T.toGrp ∧ IsMaximalTorus t ∧
      CommGroupScheme.groupHom f ≫ t = i := by
  obtain ⟨D, π, d, hd, hπ, _⟩ := hS.exists_factor_isSplitSubtorus i
  obtain ⟨T, t, ht, g, hg⟩ := exists_maximalSplitTorus_extension G d hd
  refine ⟨T, t, Additive.ofMul (π ≫ g), ht.1.1, ?_, ?_⟩
  · refine ⟨ht.1.1.isTorus, ht.1.2, ?_⟩
    intro T' t' g' hT' ht' hg'
    exact ht.2 T' t'
      ⟨hT'.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting, ht'⟩ g' hg'
  · change (π ≫ g) ≫ t = i
    rw [Category.assoc, hg, hπ]

/-- The actual identity component of a full character-kernel centralizer is
connected reductive over an algebraically closed field. -/
theorem isConnectedReductive_kernelCentralizer_identityComponent_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (a : characterLattice S) (ha : a ≠ 0)
    (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)
    (hclosed : IsClosedSubgroup j) [Smooth C.X.hom] [IsAffineHom C.X.hom] :
    IsConnectedReductive (identityComponent C) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨T, t, f, hT, ht, hfi⟩ := exists_factor_split_maximalTorus hS i
  subst i
  let t₀ := kernelCentralizerTorusFactor f t a j hj hT
  let q := identityComponentι C ≫ j
  have hq : IsClosedSubgroup q :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hclosed
  let : IsClosedImmersion q.hom.hom.left := hq
  let : Mono q.hom.hom := Over.mono_of_mono_left _
  have htq : t₀ ≫ q = t := kernelCentralizerTorusFactor_comp f t a j hj hT
  have ht₀ : IsClosedSubgroup t₀ := IsClosedSubgroup.of_comp hq (by rw [htq]; exact ht.2.1)
  have hself : torusCentralizer t₀ = SubgroupFunctor.range t₀ := by
    apply torusCentralizer_eq_range_of_comp_mono t₀ q
    rw [htq]
    exact maximalTorusCentralizer k G hG T t ht
  apply isConnectedReductive_of_contained_rootCentralizers t₀ q hq hT ht₀ hself
  intro α hα
  have hαG : α ∈ roots (t₀ ≫ q) := roots_subset_comp q t₀ hα
  have hqcent : SubgroupFunctor.range q ≤
      kernelCentralizer (CommGroupScheme.groupHom f ≫ (t₀ ≫ q)) a := by
    rw [htq, ← hj.2]
    exact SubgroupFunctor.range_le_of_factor (identityComponentι C) rfl
  have hres := root_restrict_mem_zmultiples_of_range_le_kernelCentralizer
    hS f t₀ q a hqcent hα
  let d := proportionalRootCentralizerData hG (t₀ ≫ q) hT α hα.1
  have hdC : SubgroupFunctor.range d.inclusion ≤ SubgroupFunctor.range j := by
    rw [hj.2, ← htq]
    exact range_proportionalCentralizer_le_kernelCentralizer hG (t₀ ≫ q) hT
      (by rwa [htq]) hS f a ha hαG hres
  let : ConnectedSpace d.groupScheme.X.left := by
    change ConnectedSpace
      (RankOneCentralizerDetection.groupScheme (t₀ ≫ q) hT α hα.1).X.left
    let : ConnectedSpace G.X.left := hG.connectedSpace
    infer_instance
  let lC := hj.factorHom d.inclusion (by rw [← hj.2]; exact hdC)
  let l₀ := IdentityComponent.factor C lC
  refine ⟨d, SubgroupFunctor.range_le_of_factor l₀ ?_⟩
  dsimp only [q, l₀]
  rw [IdentityComponent.factor_identityComponentι_assoc]
  exact hj.factorHom_comp d.inclusion _

end Langlands.GroupScheme.RelativeRoot
