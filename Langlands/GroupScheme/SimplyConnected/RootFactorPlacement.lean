import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductUniqueness
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimpleIrreducibleProof
import Langlands.GroupScheme.Reductive.SplitNormalRootDichotomy

/-! # Actual root-subgroup placement in simply connected product factors -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootPairNoncommutation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- All-test commutation detects zero Cartan pairing over every field, by
using the algebraic closure as a test scheme for the rank-one unit relation. -/
theorem pairing_eq_zero_of_commute_allTests (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (r r' : J)
    (hcomm : ∀ Z : Over (Spec (CommRingCat.of k)),
      ∀ x ∈ (RelativeRoot.subgroup i (P.root r)).carrier Z,
      ∀ y, (y ∈ (RelativeRoot.subgroup i (P.root r')).carrier Z ∨
        y ∈ (RelativeRoot.subgroup i (-P.root r')).carrier Z) → Commute x y) :
    P.pairing r r' = 0 := by
  let K := AlgebraicClosure k
  let Z : Over (Spec (CommRingCat.of k)) := Over.mk (algebraBaseMap k K)
  let φ : K ≃+* Γ(Z.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  apply splitTorus.eq_zero_of_forall_units_zpow_eq_one (k := K)
  intro u
  have hu : IsUnit (1 + φ ((u : K) - 1)) := by
    rw [← map_one φ, ← map_add, add_sub_cancel]
    exact u.isUnit.map φ
  have h := zpow_pairing_eq_one_of_commute hG hT hi hP r r'
    (hcomm Z) (φ ((u : K) - 1)) hu
  have hmap : Units.map φ.toMonoidHom u = hu.unit := by
    apply Units.ext
    rw [Units.coe_map, IsUnit.unit_spec, ← map_one φ, ← map_add, add_sub_cancel]
    rfl
  apply Units.map_injective (f := φ.toMonoidHom) φ.injective
  rw [map_zpow, hmap, h, map_one]

end Langlands.GroupScheme.RootPairNoncommutation

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)

include hG hT ht

/-- Every actual root subgroup lies in an actual product factor. -/
theorem exists_root_subgroup_le_factor {α : characterLattice T}
    (hα : α ∈ relativeRoots t) :
    ∃ i : D.Index, RelativeRoot.subgroup t α ≤ SubgroupFunctor.range (D.inclusion i) := by
  classical
  let : ∀ i, Smooth (D.factor i).X.hom :=
    fun i => (D.isSimplyConnected i).isSemisimple.isConnectedReductive.smooth
  let : ∀ i, ConnectedSpace (D.factor i).X.left :=
    fun i => (D.isSimplyConnected i).isSemisimple.isConnectedReductive.connectedSpace
  have hdich (i : D.Index) := splitNormalRootDichotomy hG t hT ht
    (D.inclusion i) (D.isClosedSubgroup_inclusion i) (D.isNormal_range_inclusion i) α hα
  by_contra h
  have hcent (i : D.Index) : RelativeRoot.subgroup t α ≤
      (AutomorphicAction.conjugation (D.inclusion i)).fixedSubgroup :=
    (hdich i).resolve_left (fun hi => h ⟨i, hi⟩)
  apply RelativeRoot.subgroup_not_le_torusCentralizer t hG.isConnectedReductive
    (ht.isMaximalSplitTorus hT) hα
  intro Z x hx V f s
  apply (commute_iff_eq _ _).mpr
  apply D.points_ext
  intro i
  have hc := (mem_conjugation_fixedSubgroup_iff (D.inclusion i) x).mp
    (hcent i Z hx) V f ((s ≫ t.hom.hom) ≫ (D.projection i).hom.hom)
  have he := congrArg (fun z => z ≫ (D.projection i).hom.hom) hc.symm.eq
  simpa only [MonObj.mul_comp, D.inclusion_projection_points_self] using he

/-- A nonzero actual root subgroup lies in at most one product factor. -/
theorem root_subgroup_factor_unique {α : characterLattice T}
    (hα : α ∈ relativeRoots t) {i j : D.Index}
    (hi : RelativeRoot.subgroup t α ≤ SubgroupFunctor.range (D.inclusion i))
    (hj : RelativeRoot.subgroup t α ≤ SubgroupFunctor.range (D.inclusion j)) : i = j := by
  by_contra hij
  apply RelativeRoot.subgroup_not_le_torusCentralizer t hG.isConnectedReductive
    (ht.isMaximalSplitTorus hT) hα
  intro Z x hx
  have hx1 : x = 1 := by
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hi Z hx)
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp (hj Z hx)
    have he := congrArg (fun w => w ≫ (D.projection i).hom.hom) (hy.trans hz.symm)
    have hy1 : y = 1 := by
      simpa only [D.inclusion_projection_points_self,
        D.inclusion_projection_points_ne j i (Ne.symm hij)] using he
    rw [← hy, hy1, MonObj.one_comp]
  rw [hx1]
  exact ((torusCentralizer t).carrier Z).one_mem

/-- The unique actual factor carrying a specified root subgroup. -/
def rootFactorIndex {α : characterLattice T} (hα : α ∈ relativeRoots t) : D.Index :=
  Classical.choose (D.exists_root_subgroup_le_factor hG hT t ht hα)

/-- The root subgroup is contained in its chosen actual product factor. -/
theorem root_subgroup_le_rootFactorIndex {α : characterLattice T}
    (hα : α ∈ relativeRoots t) :
    RelativeRoot.subgroup t α ≤ SubgroupFunctor.range
      (D.inclusion (D.rootFactorIndex hG hT t ht hα)) :=
  Classical.choose_spec (D.exists_root_subgroup_le_factor hG hT t ht hα)

/-- The assigned index is characterized by actual all-test subgroup containment. -/
theorem rootFactorIndex_eq_iff {α : characterLattice T}
    (hα : α ∈ relativeRoots t) (i : D.Index) :
    D.rootFactorIndex hG hT t ht hα = i ↔
      RelativeRoot.subgroup t α ≤ SubgroupFunctor.range (D.inclusion i) := by
  constructor
  · intro h
    exact h ▸ D.root_subgroup_le_rootFactorIndex hG hT t ht hα
  · exact fun hi => D.root_subgroup_factor_unique hG hT t ht hα
      (D.root_subgroup_le_rootFactorIndex hG hT t ht hα) hi

variable {J : Type u}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hP : IsRootDatumOf t P)

include hP

/-- A root of a supplied actual datum is assigned to the factor carrying its root subgroup. -/
def rootDatumFactorIndex (r : J) : D.Index :=
  D.rootFactorIndex hG hT t ht (show P.root r ∈ relativeRoots t from by
    rw [relativeRoots_eq_roots, ← hP.2.1]
    exact Set.mem_range_self r)

/-- Inside and outside a normal product factor, actual root pairings are zero. -/
theorem pairing_eq_zero_of_root_le_and_not_le (i : D.Index) (r s : J)
    (hr : RelativeRoot.subgroup t (P.root r) ≤ SubgroupFunctor.range (D.inclusion i))
    (hs : ¬ RelativeRoot.subgroup t (P.root s) ≤ SubgroupFunctor.range (D.inclusion i)) :
    P.pairing r s = 0 := by
  let H := D.factor i
  let j := D.inclusion i
  let : Smooth H.X.hom := (D.isSimplyConnected i).isSemisimple.isConnectedReductive.smooth
  let : ConnectedSpace H.X.left :=
    (D.isSimplyConnected i).isSemisimple.isConnectedReductive.connectedSpace
  have hroot (a : J) : P.root a ∈ relativeRoots t := by
    rw [relativeRoots_eq_roots, ← hP.2.1]
    exact Set.mem_range_self a
  have hdich := splitNormalRootDichotomy hG t hT ht j
    (D.isClosedSubgroup_inclusion i) (D.isNormal_range_inclusion i)
  have hfix (a : J)
      (ha : ¬ RelativeRoot.subgroup t (P.root a) ≤ SubgroupFunctor.range j) :
      RelativeRoot.subgroup t (P.root a) ≤ (AutomorphicAction.conjugation j).fixedSubgroup :=
    (hdich _ (hroot a)).resolve_left ha
  have hcomm (Z : Over (Spec (CommRingCat.of k))) (x y : Z ⟶ G.X)
      (hx : x ∈ (SubgroupFunctor.range j).carrier Z)
      (hy : y ∈ (AutomorphicAction.conjugation j).fixedSubgroup.carrier Z) :
      Commute x y := by
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have h := (mem_conjugation_fixedSubgroup_iff j y).mp hy Z (𝟙 Z) z
    simpa only [Category.id_comp] using h
  have hneg (a b : J)
      (ha : ¬ RelativeRoot.subgroup t (P.root a) ≤ SubgroupFunctor.range j)
      (hb : P.root b = -P.root a) :
      ¬ RelativeRoot.subgroup t (P.root b) ≤ SubgroupFunctor.range j := by
    intro hbin
    have hzero := RootPairNoncommutation.pairing_eq_zero_of_commute_allTests
      hG.isConnectedReductive hT ht hP b a (fun Z x hx y hy => by
        rcases hy with hy | hy
        · exact hcomm Z x y (hbin Z hx) (hfix a ha Z hy)
        · rw [← hb] at hy
          exact RootPairNoncommutation.commute_of_mem_same_root
            hG.isConnectedReductive hT ht hP b hx hy)
    have hpair : P.pairing b a = -2 := by
      rw [← P.root_coroot_eq_pairing, hb, map_neg, LinearMap.neg_apply,
        P.root_coroot_eq_pairing, RootPairing.pairing_same]
    rw [hpair] at hzero
    norm_num at hzero
  obtain ⟨s', hs'⟩ : -P.root s ∈ Set.range P.root :=
    P.neg_mem_range_root_iff.mpr (Set.mem_range_self s)
  have hsout := hneg s s' hs hs'
  apply RootPairNoncommutation.pairing_eq_zero_of_commute_allTests hG.isConnectedReductive hT ht hP r s
  intro Z x hx y hy
  rcases hy with hy | hy
  · exact hcomm Z x y (hr Z hx) (hfix s hs Z hy)
  · rw [← hs'] at hy
    exact hcomm Z x y (hr Z hx) (hfix s' hsout Z hy)

/-- Roots assigned to different actual product factors have zero ordered Cartan pairing. -/
theorem pairing_eq_zero_of_rootDatumFactorIndex_ne (r s : J)
    (hrs : D.rootDatumFactorIndex hG hT t ht hP r ≠
      D.rootDatumFactorIndex hG hT t ht hP s) : P.pairing r s = 0 := by
  apply D.pairing_eq_zero_of_root_le_and_not_le hG hT t ht hP
    (D.rootDatumFactorIndex hG hT t ht hP r) r s
  · exact D.root_subgroup_le_rootFactorIndex hG hT t ht _
  · intro hs
    apply hrs
    exact (D.rootFactorIndex_eq_iff hG hT t ht _ _).mpr hs |>.symm

/-- Connected simple vertices of the actual Cartan diagram are carried by the
same actual simply connected almost-simple product factor. -/
theorem rootDatumFactorIndex_eq_of_cartanConnected (b : P.Base) {a c : b.support}
    (h : Relation.EqvGen (fun x y : b.support => x ≠ y ∧ P.pairing x.val y.val ≠ 0) a c) :
    D.rootDatumFactorIndex hG hT t ht hP a.val =
      D.rootDatumFactorIndex hG hT t ht hP c.val := by
  induction h with
  | rel a c hac =>
    by_contra hne
    exact hac.2 (D.pairing_eq_zero_of_rootDatumFactorIndex_ne hG hT t ht hP a.val c.val hne)
  | refl a => rfl
  | symm a c _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
