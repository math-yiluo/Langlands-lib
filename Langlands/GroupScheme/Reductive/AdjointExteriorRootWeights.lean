import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Langlands.LinearAlgebra.RootDatumZeroFace

/-! # Finite-subset weight comparison for adjoint exterior powers -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RootDatumZeroFace

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

private def omittedSimpleIndices (O : Finset p.base.support) : Finset p.rootIndex :=
  O.map (Function.Embedding.subtype (· ∈ p.base.support))

section Subset

variable [Fintype p.rootIndex] {n : Type} (r : p.rootIndex ↪ n)
  (O : Finset p.base.support)

open Classical in
private theorem omittedSimpleIndices_subset_positive :
    p.omittedSimpleIndices O ⊆ Finset.univ.filter p.base.IsPos := by
  intro i hi
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.base.isPos_of_mem_support a.property⟩

open Classical in
/-- The indices of the positive roots other than the selected simple roots,
transported along the root embedding into the ambient index type. -/
def positiveRootComplementIndices : Finset n :=
  ((Finset.univ.filter p.base.IsPos) \ p.omittedSimpleIndices O).map r

open Classical in
/-- The complementary positive-root subset has the exterior degree given by
the number of positive roots minus the number of omitted simple roots. -/
theorem positiveRootComplementIndices_card :
    (p.positiveRootComplementIndices r O).card =
      (Finset.univ.filter p.base.IsPos).card - O.card := by
  rw [positiveRootComplementIndices, Finset.card_map,
    Finset.card_sdiff_of_subset (p.omittedSimpleIndices_subset_positive O)]
  simp only [omittedSimpleIndices, Finset.card_map]

/-- The sum over the complementary positive-root subset is the published sum
of positive roots minus the sum of the omitted simple roots. -/
theorem sum_positiveRootComplementIndices (w : n → characterLattice p.torus)
    (hr : ∀ i, w (r i) = p.rootDatum.root i) :
    ∑ i ∈ p.positiveRootComplementIndices r O, w i =
      IntegralWeylVector.positiveRootSum p.rootDatum p.base - ∑ i ∈ O, p.rootDatum.root i := by
  classical
  rw [positiveRootComplementIndices, Finset.sum_map, IntegralWeylVector.positiveRootSum]
  simp_rw [hr]
  have hadd := Finset.sum_sdiff (f := p.rootDatum.root)
    (p.omittedSimpleIndices_subset_positive O)
  rw [omittedSimpleIndices, Finset.sum_map] at hadd
  exact eq_sub_of_add_eq hadd

end Subset

open Classical in
private def complementCoefficient (O : Finset p.base.support) (i : p.rootIndex) : ℤ :=
  if i ∈ p.omittedSimpleIndices O then 1 else 2

private theorem complementCoefficient_pos (O : Finset p.base.support) (i : p.rootIndex) :
    0 < p.complementCoefficient O i := by
  unfold complementCoefficient
  split <;> decide

private def complementDegree (O : Finset p.base.support) : p.rootDatum.rootSpan ℤ →ₗ[ℤ] ℤ :=
  p.base.toWeightBasisInt.constr ℤ (fun i => p.complementCoefficient O i)

private theorem complementDegree_simple (O : Finset p.base.support) (i : p.base.support) :
    p.complementDegree O (p.rootDatum.rootSpanMem ℤ i) = p.complementCoefficient O i := by
  have h : p.rootDatum.rootSpanMem ℤ i = p.base.toWeightBasisInt i := by
    apply Subtype.ext
    simp
  rw [h, complementDegree, Module.Basis.constr_basis]

private theorem complementDegree_eq_sum (O : Finset p.base.support)
    (x : p.rootDatum.rootSpan ℤ) (f : p.rootIndex → ℕ)
    (hx : (x : characterLattice p.torus) = ∑ j ∈ p.base.support, f j • p.rootDatum.root j) :
    p.complementDegree O x = ∑ j ∈ p.base.support, (f j : ℤ) * p.complementCoefficient O j := by
  have hlift : x = ∑ j ∈ p.base.support, f j • p.rootDatum.rootSpanMem ℤ j := by
    apply Subtype.ext
    simpa using hx
  rw [hlift, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_nsmul, p.complementDegree_simple O ⟨j, hj⟩, nsmul_eq_mul]

private theorem complementDegree_nonneg_of_mem_closure (O : Finset p.base.support)
    (x : p.rootDatum.rootSpan ℤ)
    (hx : (x : characterLattice p.torus) ∈
      AddSubmonoid.closure (p.rootDatum.root '' p.base.support)) :
    0 ≤ p.complementDegree O x := by
  obtain ⟨f, hf⟩ := exists_nat_of_mem_closure p.base hx
  rw [p.complementDegree_eq_sum O x f hf]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (Int.natCast_nonneg _) (p.complementCoefficient_pos O j).le

private theorem mem_omittedSimpleIndices_of_degree_le_one (O : Finset p.base.support)
    (i : p.rootIndex) (hi : p.base.IsPos i)
    (hdeg : p.complementDegree O (p.rootDatum.rootSpanMem ℤ i) ≤ 1) :
    i ∈ p.omittedSimpleIndices O := by
  classical
  obtain ⟨f, hf⟩ := exists_nat_of_mem_closure p.base ((isPos_iff_mem_closure p.base i).mp hi)
  have hsome : ∃ j ∈ p.base.support, 0 < f j := by
    by_contra! h
    have hz : ∑ j ∈ p.base.support, f j • p.rootDatum.root j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Nat.eq_zero_of_le_zero (h j hj), zero_nsmul]
    exact p.rootDatum.ne_zero i (hf.trans hz)
  obtain ⟨j, hj, hfj⟩ := hsome
  let term : p.rootIndex → ℤ := fun a => (f a : ℤ) * p.complementCoefficient O a
  have hnonneg (a : p.rootIndex) : 0 ≤ term a :=
    mul_nonneg (Int.natCast_nonneg _) (p.complementCoefficient_pos O a).le
  have hsum : ∑ a ∈ p.base.support, term a ≤ 1 := by
    rwa [p.complementDegree_eq_sum O (p.rootDatum.rootSpanMem ℤ i) f hf] at hdeg
  have hsplit := p.base.support.sum_erase_add term hj
  have hrest_nonneg : 0 ≤ ∑ a ∈ p.base.support.erase j, term a :=
    Finset.sum_nonneg fun a _ => hnonneg a
  have hterm_pos : 0 < term j :=
    mul_pos (by exact_mod_cast hfj) (p.complementCoefficient_pos O j)
  have hterm_one : term j = 1 := by omega
  have hjO : j ∈ p.omittedSimpleIndices O := by
    by_contra hjO
    have ht : term j = (f j : ℤ) * 2 := by simp [term, complementCoefficient, hjO]
    omega
  have hfj_one : f j = 1 := by
    have h : term j = (f j : ℤ) := by simp [term, complementCoefficient, hjO]
    omega
  have hrest_zero : ∑ a ∈ p.base.support.erase j, term a = 0 := by omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnonneg a)).mp hrest_zero
  have hroot : p.rootDatum.root i = p.rootDatum.root j := by
    rw [hf, Finset.sum_eq_single_of_mem j hj]
    · rw [hfj_one, one_nsmul]
    · intro a ha hne
      have ha0 := hz a (Finset.mem_erase.mpr ⟨hne, ha⟩)
      have hf0 : (f a : ℤ) = 0 :=
        (mul_eq_zero.mp ha0).resolve_right (p.complementCoefficient_pos O a).ne'
      have : f a = 0 := by exact_mod_cast hf0
      simp [this]
  rwa [p.rootDatum.root.injective hroot]

private theorem complementDegree_nonpos_of_not_pos (O : Finset p.base.support)
    (i : p.rootIndex) (hi : ¬ p.base.IsPos i) :
    p.complementDegree O (p.rootDatum.rootSpanMem ℤ i) ≤ 0 := by
  let j := p.rootDatum.reflectionPerm i i
  have hj : (p.rootDatum.rootSpanMem ℤ j : characterLattice p.torus) ∈
      AddSubmonoid.closure (p.rootDatum.root '' p.base.support) :=
    show p.rootDatum.root j ∈ _ by
      rw [show j = _ by rfl, p.rootDatum.root_reflectionPerm, p.rootDatum.reflection_apply_self]
      exact (neg_mem_closure_iff_not_isPos p.base i).mpr hi
  have h := p.complementDegree_nonneg_of_mem_closure O (p.rootDatum.rootSpanMem ℤ j) hj
  rwa [show j = _ by rfl, p.rootDatum.rootSpanMem_reflectionPerm_self, map_neg, neg_nonneg] at h

open Classical in
private theorem one_lt_complementDegree_iff (O : Finset p.base.support) (i : p.rootIndex) :
    1 < p.complementDegree O (p.rootDatum.rootSpanMem ℤ i) ↔
      p.base.IsPos i ∧ i ∉ p.omittedSimpleIndices O := by
  constructor
  · intro h
    have hi : p.base.IsPos i := by
      by_contra hn
      have hnonpos := p.complementDegree_nonpos_of_not_pos O i hn
      omega
    refine ⟨hi, ?_⟩
    intro hiO
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hiO
    change 1 < p.complementDegree O (p.rootDatum.rootSpanMem ℤ (a : p.rootIndex)) at h
    rw [p.complementDegree_simple O a] at h
    have ha' : (a : p.rootIndex) ∈ p.omittedSimpleIndices O :=
      Finset.mem_map.mpr ⟨a, ha, rfl⟩
    simp [complementCoefficient, ha'] at h
  · rintro ⟨hi, hiO⟩
    exact lt_of_not_ge fun h => hiO (p.mem_omittedSimpleIndices_of_degree_le_one O i hi h)

section Compare

variable [Fintype p.rootIndex] {n : Type} (r : p.rootIndex ↪ n)
  (O : Finset p.base.support) (w : n → characterLattice p.torus)

/-- Among subsets of the same size, every other subset yields a difference
from the complementary positive-root sum outside the simple-root monoid.
Each root occurs at its embedded index, and other indices have weight zero. -/
theorem sub_sum_not_mem_positiveRootMonoid
    (hr : ∀ i, w (r i) = p.rootDatum.root i)
    (hzero : ∀ i, i ∉ Set.range r → w i = 0)
    (T : Finset n) (hcard : T.card = (p.positiveRootComplementIndices r O).card)
    (hne : T ≠ p.positiveRootComplementIndices r O) :
    (∑ i ∈ T, w i) - (∑ i ∈ p.positiveRootComplementIndices r O, w i) ∉
      p.positiveRootMonoid := by
  classical
  let S := p.positiveRootComplementIndices r O
  have hw (i : n) : w i ∈ p.rootDatum.rootSpan ℤ := by
    by_cases hi : i ∈ Set.range r
    · obtain ⟨a, rfl⟩ := hi
      rw [hr]
      exact (p.rootDatum.rootSpanMem ℤ a).property
    · rw [hzero i hi]
      exact Submodule.zero_mem _
  let liftWeight (i : n) : p.rootDatum.rootSpan ℤ := ⟨w i, hw i⟩
  let degree := p.complementDegree O
  let score := fun i => degree (liftWeight i)
  have hscore (i : n) : 1 < score i ↔ i ∈ S := by
    by_cases hi : i ∈ Set.range r
    · obtain ⟨a, rfl⟩ := hi
      have hlift : liftWeight (r a) = p.rootDatum.rootSpanMem ℤ a := Subtype.ext (hr a)
      change 1 < p.complementDegree O (liftWeight (r a)) ↔ r a ∈ S
      rw [hlift, p.one_lt_complementDegree_iff O a]
      simp [S, positiveRootComplementIndices]
    · have hlift : liftWeight i = 0 := Subtype.ext (hzero i hi)
      have hnot : i ∉ S := by
        intro hm
        obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hm
        exact hi ⟨a, ha⟩
      simp [score, hlift, hnot]
  have hdiffcard : (T \ S).card = (S \ T).card :=
    Finset.card_sdiff_eq_card_sdiff_iff.mpr hcard
  have hdiff_nonempty : (S \ T).Nonempty := Finset.sdiff_nonempty.mpr fun hsub =>
    hne (Finset.eq_of_subset_of_card_le hsub hcard.le).symm
  have hlt : ∑ i ∈ T \ S, score i < ∑ i ∈ S \ T, score i := calc
    ∑ i ∈ T \ S, score i ≤ ∑ _i ∈ T \ S, (1 : ℤ) := by
      refine Finset.sum_le_sum fun i hi => le_of_not_gt ?_
      exact fun h => (Finset.mem_sdiff.mp hi).2 ((hscore i).mp h)
    _ = ∑ _i ∈ S \ T, (1 : ℤ) := by simp [hdiffcard]
    _ < ∑ i ∈ S \ T, score i :=
      Finset.sum_lt_sum_of_nonempty hdiff_nonempty fun i hi =>
        (hscore i).mpr (Finset.mem_sdiff.mp hi).1
  have hT : (∑ i ∈ T \ S, score i) + (∑ i ∈ S ∩ T, score i) = ∑ i ∈ T, score i := by
    simpa only [Finset.sdiff_inter_self_right] using
      (Finset.sum_sdiff (f := score) (Finset.inter_subset_right : S ∩ T ⊆ T))
  have hS : (∑ i ∈ S \ T, score i) + (∑ i ∈ S ∩ T, score i) = ∑ i ∈ S, score i := by
    simpa only [Finset.sdiff_inter_self_left] using
      (Finset.sum_sdiff (f := score) (Finset.inter_subset_left : S ∩ T ⊆ S))
  have hsum_lt : ∑ i ∈ T, score i < ∑ i ∈ S, score i := by omega
  let x := (∑ i ∈ T, liftWeight i) - (∑ i ∈ S, liftWeight i)
  have hx : (x : characterLattice p.torus) = (∑ i ∈ T, w i) - (∑ i ∈ S, w i) := by
    simp [x, liftWeight]
  have hgen : Set.range (fun a : p.base.support => p.rootDatum.root a) =
      p.rootDatum.root '' (p.base.support : Set p.rootIndex) := by
    ext y
    exact ⟨fun ⟨a, ha⟩ => ⟨a, a.property, ha⟩, fun ⟨a, ha, hy⟩ => ⟨⟨a, ha⟩, hy⟩⟩
  intro hmem
  have hxmem : (x : characterLattice p.torus) ∈
      AddSubmonoid.closure (p.rootDatum.root '' p.base.support) := by
    rw [← hgen]
    change (x : characterLattice p.torus) ∈ p.positiveRootMonoid
    rwa [hx]
  have hnonneg := p.complementDegree_nonneg_of_mem_closure O x hxmem
  change 0 ≤ degree x at hnonneg
  rw [show x = _ by rfl, map_sub, map_sum, map_sum] at hnonneg
  change 0 ≤ (∑ i ∈ T, score i) - (∑ i ∈ S, score i) at hnonneg
  omega

end Compare

end Langlands.GroupScheme.SplitPinning
