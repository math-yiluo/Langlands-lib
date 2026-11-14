import Langlands.GroupScheme.Reductive.SplitIsogenySimpleGraph
import Langlands.GroupScheme.Reductive.SplitLeviGluingMixedRoots
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Mixed simple roots for a restricted target-torus action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (t : T ⟶ T')
    {J J' : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (ν : cocharacterLattice T) (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (hν : IsGenericCocharacter i ν)

omit [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom] in
include hP hν hT in
/-- Every actual source root has one sign in the nonnegative simple-root monoid. -/
theorem root_or_neg_mem_simpleClosure {β : characterLattice T} (hβ : β ∈ roots i) :
    β ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) ∨
      -β ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) := by
  rw [LeviGluing.closure_simpleRoots_eq_positive i P hP ν hT]
  rcases lt_or_gt_of_ne (hν β hβ) with hneg | hpos
  · right
    apply AddSubmonoid.subset_closure
    refine ⟨?_, ?_⟩
    · change -β ∈ roots i
      rw [← hP.2.1]
      exact P.neg_mem_range_root_iff.mpr (by rwa [hP.2.1])
    · simpa only [map_neg, LinearMap.neg_apply] using neg_pos.mpr hneg
  · exact Or.inl (AddSubmonoid.subset_closure ⟨hβ, hpos⟩)

omit [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom] in
include hP hν hT in
/-- A strict mixed combination is not even a nonnegative integral multiple
of any actual source root. -/
theorem mixedRootSemigroup_ne_rootMultiple
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    {x : characterLattice T} (hx : x ∈ LeviGluing.mixedRootSemigroup a b)
    {β : characterLattice T} (hβ : β ∈ roots i) (q : ℕ) : q • β ≠ x := by
  obtain ⟨n, m, hn, hm, rfl⟩ := (LeviGluing.mem_mixedRootSemigroup_iff _ _ _).mp hx
  obtain ⟨hpos, hneg⟩ :=
    LeviGluing.mixed_simple_not_mem_positive i P hP ν hT hν a b hab n m hn hm
  intro heq
  rcases root_or_neg_mem_simpleClosure i P hP ν hT hν hβ with h | h
  · exact hpos (heq ▸ (AddSubmonoid.closure _).nsmul_mem h q)
  · apply hneg
    rw [← heq, ← smul_neg]
    exact (AddSubmonoid.closure _).nsmul_mem h q

section Isogeny

variable [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    [P.IsReduced] [P'.IsReduced] {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hw : ∀ χ : characterLattice T', t ≫ χ = f.weightMap χ)

include hP hP' hν hT hT' hw in
/-- The target action restricted to the source torus has no mixed
source-simple weights. Root factors may be arbitrary characteristic powers. -/
theorem restricted_mixedRootSemigroup_has_no_roots
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    {x : characterLattice T} (hx : x ∈ LeviGluing.mixedRootSemigroup a b) :
    x ≠ 0 ∧ x ∉ roots (CommGroupScheme.groupHom t ≫ i') := by
  refine ⟨(LeviGluing.mixedRootSemigroup_has_no_roots i P hP ν hT hν a b hab hx).1, ?_⟩
  intro hroot
  obtain ⟨_, χ, hχ, hχx⟩ := (mem_roots_comp_iff hT' hT t i' x).mp hroot
  rw [← hP'.2.1] at hχ
  obtain ⟨j, rfl⟩ := hχ
  have heq : f.rootFactor j • P.root (f.indexEquiv j) = x := by
    simpa only [hw, f.root_weightMap, natCast_zsmul] using hχx
  exact mixedRootSemigroup_ne_rootMultiple i P hP ν hT hν a b hab hx
    (by rw [← hP.2.1]; exact ⟨f.indexEquiv j, rfl⟩) (f.rootFactor j) heq

include hP hP' hν hT hT' hw in
/-- The mixed semigroup subgroup of the restricted target action is trivial
on all tests, including nonreduced schemes. -/
theorem restricted_mixedRoot_semigroupSubgroup_eq_bot
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b) :
    RelativeRoot.semigroupSubgroup
      (AutomorphicAction.conjugation (CommGroupScheme.groupHom t ≫ i'))
      (LeviGluing.mixedRootSemigroup a b) = ⊥ := by
  apply RelativeRoot.semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization
    (AutomorphicAction.conjugation (CommGroupScheme.groupHom t ≫ i')) hT
  intro x hx hweight
  obtain ⟨hx0, hxroot⟩ := restricted_mixedRootSemigroup_has_no_roots
    i i' t P P' hP hP' ν hT hT' hν f hw a b hab hx
  exact hxroot ((RelativeRoot.mem_actionWeightSupport_conjugation_iff _ hx0).mp hweight)

include hP hP' hν hT hT' hw in
/-- Restricted target root functors at distinct source simple/opposite
characters commute on every scheme test. -/
theorem commute_restricted_simple_opposite [Smooth G'.X.hom]
    (a b : simpleRelativeRoots i ν) (hab : a ≠ b)
    {W : Over (Spec (CommRingCat.of k))} {x y : W ⟶ G'.X}
    (hx : x ∈ (RelativeRoot.subgroup (CommGroupScheme.groupHom t ≫ i') a).carrier W)
    (hy : y ∈ (RelativeRoot.subgroup (CommGroupScheme.groupHom t ≫ i')
      (-(b : characterLattice T))).carrier W) : Commute x y := by
  let j := CommGroupScheme.groupHom t ≫ i'
  let c := AutomorphicAction.conjugation j
  have hx' : x ∈ (RelativeRoot.semigroupSubgroup c
      (RelativeRoot.cyclicTail (a : characterLattice T) 1)).carrier W := by
    change x ∈ (RelativeRoot.weightFiltration c (a : characterLattice T) 1).carrier W
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT j _ a.2.1.1.1]
    exact hx
  have hy' : y ∈ (RelativeRoot.semigroupSubgroup c
      (RelativeRoot.cyclicTail (-(b : characterLattice T)) 1)).carrier W := by
    change y ∈ (RelativeRoot.weightFiltration c (-(b : characterLattice T)) 1).carrier W
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT j _ (neg_ne_zero.mpr b.2.1.1.1)]
    exact hy
  have h := RelativeRoot.semigroupCommutator k G' inferInstance inferInstance T hT c
    (RelativeRoot.cyclicTail (a : characterLattice T) 1)
    (RelativeRoot.cyclicTail (-(b : characterLattice T)) 1) W x y hx' hy'
  change x * y * x⁻¹ * y⁻¹ ∈ (RelativeRoot.semigroupSubgroup
    (AutomorphicAction.conjugation (CommGroupScheme.groupHom t ≫ i'))
    (LeviGluing.mixedRootSemigroup a b)).carrier W at h
  rw [restricted_mixedRoot_semigroupSubgroup_eq_bot
    i i' t P P' hP hP' ν hT hT' hν f hw a b hab] at h
  have heq : x * y * x⁻¹ * y⁻¹ = 1 := h
  exact commutatorElement_eq_one_iff_commute.mp heq

variable [Smooth G.X.hom] [Smooth G'.X.hom]

namespace SimpleIsogenyGraph

variable {i i' t} (D : SimpleIsogenyGraph i i' t)

include hP hP' hT' hw in
/-- Distinct source-simple positive and negative lifts commute in the actual
graph, even when the target root characters differ by characteristic powers. -/
theorem commute_positive_negative
    (a b : D.SimpleIndex) (hab : a ≠ b)
    {W : Over (Spec (CommRingCat.of k))} {x y : W ⟶ D.envelope.group.X}
    (hx : x ∈ (SubgroupFunctor.range (D.positiveHom a)).carrier W)
    (hy : y ∈ (SubgroupFunctor.range (D.negativeHom b)).carrier W) : Commute x y := by
  have hx0 := D.envelope.range_rootLift_le a (D.positiveRoot a) W hx
  have hy0 := D.envelope.range_rootLift_le b (D.negativeRoot b) W hy
  have hx1 := RelativeRoot.comp_mem_subgroup D.envelope.torusLift
    (a : characterLattice T) D.envelope.first hx0
  have hy1 := RelativeRoot.comp_mem_subgroup D.envelope.torusLift
    (-(b : characterLattice T)) D.envelope.first hy0
  rw [D.envelope.torusLift_first] at hx1 hy1
  have hc1 := LeviGluing.commute_simple_opposite i P hP D.directions.chamber
    D.split D.directions.generic a b hab hx1 hy1
  have hx2 := RelativeRoot.comp_mem_subgroup D.envelope.torusLift
    (a : characterLattice T) D.envelope.second hx0
  have hy2 := RelativeRoot.comp_mem_subgroup D.envelope.torusLift
    (-(b : characterLattice T)) D.envelope.second hy0
  rw [D.envelope.torusLift_second] at hx2 hy2
  have hc2 := commute_restricted_simple_opposite i i' t P P' hP hP'
    D.directions.chamber D.split hT' D.directions.generic f hw a b hab hx2 hy2
  change x * y = y * x
  apply D.envelope.points_ext
  · simpa only [MonObj.mul_comp] using hc1.eq
  · simpa only [MonObj.mul_comp] using hc2.eq

end SimpleIsogenyGraph

/-- An actual source-simple graph with its all-test distinct-index
commutation certificate. -/
structure CommutingSimpleIsogenyGraph where
  graph : SimpleIsogenyGraph i i' t
  commutes : ∀ (a b : graph.SimpleIndex), a ≠ b →
    ∀ {W : Over (Spec (CommRingCat.of k))} {x y : W ⟶ graph.envelope.group.X},
      x ∈ (SubgroupFunctor.range (graph.positiveHom a)).carrier W →
      y ∈ (SubgroupFunctor.range (graph.negativeHom b)).carrier W → Commute x y

include hP hP' hT' hw in
/-- Certify actual graph commutation using both root data and the prescribed
character map, without assuming target simple-root transport. -/
def commutingSimpleIsogenyGraph (D : SimpleIsogenyGraph i i' t) :
    CommutingSimpleIsogenyGraph i i' t :=
  ⟨D, D.commute_positive_negative P P' hP hP' hT' f hw⟩

end Isogeny

end Langlands.GroupScheme.RootDatumIsogenyRealization
