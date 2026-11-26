import Langlands.LinearAlgebra.GMFamilyRootGeometry
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Baire.Lemmas

/-! # Adjacent chambers in a Levi flat -/

noncomputable section

open scoped RealInnerProductSpace
open Classical
open Set

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def indecomposable {V : Type*} [Add V] (P : Finset V) : Finset V :=
  P.filter fun v => ¬ ∃ u ∈ P, ∃ w ∈ P, v = u + w

private theorem mem_indec {V : Type*} [Add V] {P : Finset V} {x : V} :
    x ∈ indecomposable P ↔ x ∈ P ∧ ¬ ∃ u ∈ P, ∃ w ∈ P, x = u + w := Finset.mem_filter

private theorem finite_positive_induction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : Finset V) (f : V →ₗ[ℝ] ℝ) (hpos : ∀ v ∈ P, 0 < f v) {C : V → Prop}
    (step : ∀ v ∈ P, (∀ u ∈ P, ∀ w ∈ P, v = u + w → C u ∧ C w) → C v)
    (v : V) (hv : v ∈ P) : C v := by
  let m (x : V) := (P.filter fun y => f y < f x).card
  induction v using (measure m).wf.induction with
  | h v ih =>
    apply step v hv
    intro u hu w hw he
    have hlt (x : V) (hx : x ∈ P) (hxv : f x < f v) : m x < m v := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨hzP, hzlt⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzP, hzlt.trans hxv⟩
      · intro heq
        have hxin : x ∈ P.filter (fun y => f y < f v) := Finset.mem_filter.mpr ⟨hx, hxv⟩
        rw [← heq] at hxin
        exact (lt_irrefl _) (Finset.mem_filter.mp hxin).2
    have he' : f v = f u + f w := by rw [he, map_add]
    have hlu : f u < f v := by linarith [hpos w hw]
    have hlw : f w < f v := by linarith [hpos u hu]
    exact ⟨ih u (hlt u hu hlu) hu, ih w (hlt w hw hlw) hw⟩

private theorem exists_natCombination {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : Finset V) (f : V →ₗ[ℝ] ℝ) (hpos : ∀ v ∈ P, 0 < f v) {v : V} (hv : v ∈ P) :
    ∃ n : indecomposable P → ℕ, v = ∑ i, n i • (i : V) := by
  refine finite_positive_induction P f hpos (C := fun x => ∃ n : indecomposable P → ℕ,
    x = ∑ i, n i • (i : V)) (fun x hx ih => ?_) v hv
  by_cases hi : x ∈ indecomposable P
  · refine ⟨fun i => if i = ⟨x, hi⟩ then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single ⟨x, hi⟩] <;> simp +contextual
  · have hsplit : ∃ u ∈ P, ∃ w ∈ P, x = u + w := by
      by_contra hn
      exact hi (Finset.mem_filter.mpr ⟨hx, hn⟩)
    obtain ⟨u, hu, w, hw, he⟩ := hsplit
    obtain ⟨⟨nu, hnu⟩, ⟨nw, hnw⟩⟩ := ih u hu w hw he
    exact ⟨fun i => nu i + nw i,
      by rw [he, hnu, hnw]; simp only [add_nsmul, Finset.sum_add_distrib]⟩

section HyperplaneAvoidance

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The complement of finitely many proper real linear hyperplanes is dense. -/
theorem dense_nonzero_forms (s : Finset ι) (l : ι → V →L[ℝ] ℝ)
    (hn : ∀ i ∈ s, l i ≠ 0) : Dense {x | ∀ i ∈ s, l i x ≠ 0} := by
  let U (i : ι) : Set V := {x | l i x ≠ 0}
  have hU (i : ι) : IsOpen (U i) := isOpen_ne_fun (l i).continuous continuous_const
  have hd (i : ι) (hi : i ∈ s) : Dense (U i) := by
    let W := (l i).ker
    have hW : W ≠ ⊤ := fun h => hn i hi (by
      ext x
      have hx : x ∈ W := h ▸ Submodule.mem_top
      exact hx)
    have hint : interior (W : Set V) = ∅ := by
      by_contra h
      exact hW (W.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr h))
    exact interior_eq_empty_iff_dense_compl.mp hint
  have h := (s.finite_toSet.image U).dense_sInter
    (by rintro _ ⟨i, _, rfl⟩; exact hU i) (by rintro _ ⟨i, hi, rfl⟩; exact hd i hi)
  simpa only [sInter_image, mem_iInter, Finset.mem_coe, U, mem_ofPred_eq, ofPred_forall] using h

end HyperplaneAvoidance

variable [FiniteDimensional ℝ E]

private theorem mem_parabolics_posSet {R : Finset E} {a : Submodule ℝ E} {h : E}
    (hh : IsRegular R a h) : posSet R h ∈ parabolics R a := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  exact ⟨h, hh, rfl⟩

private theorem simpleRoots_eq_indec (a : Submodule ℝ E) (S : Finset E) :
    simpleRoots a S = indecomposable (restrictedRoots a S) := by
  ext x
  simp only [simpleRoots, indecomposable, Finset.mem_filter]

/-- Every restricted positive root is a natural combination of the restricted simple roots. -/
theorem exists_simpleRoot_combination {R : Finset E} {a : Submodule ℝ E} {S : Finset E}
    (hS : S ∈ parabolics R a) {x : a} (hx : x ∈ restrictedRoots a S) :
    ∃ n : simpleRoots a S → ℕ, x = ∑ i, n i • (i : a) := by
  obtain ⟨_, ⟨h, hh, rfl⟩⟩ := Finset.mem_filter.mp hS
  rw [simpleRoots_eq_indec]
  refine exists_natCombination _ (innerₛₗ ℝ (⟨h, hh.1⟩ : a)) (fun y hy => ?_) hx
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hy
  change 0 < ⟪(⟨h, hh.1⟩ : a), restrictedRoot a α⟫
  rw [real_inner_comm, inner_restrictedRoot_subtype]
  exact (Finset.mem_filter.mp hα).2

/-- A simple root of a chamber is strictly positive at its chamber vector. -/
theorem simpleRoot_pos {R : Finset E} {a : Submodule ℝ E} {h : a} {v : a}
    (hv : v ∈ simpleRoots a (posSet R h)) : 0 < ⟪v, h⟫ := by
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hv).1
  rw [inner_restrictedRoot_subtype]
  exact (Finset.mem_filter.mp hα).2

/-- Projection along the span of the family members it kills preserves independence
of the remaining members. -/
theorem linearIndependent_nonzero_map {ι V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {v : ι → V} (hv : LinearIndependent ℝ v)
    (q : V →ₗ[ℝ] W) (hk : q.ker ≤ Submodule.span ℝ (v '' {i | q (v i) = 0})) :
    LinearIndependent ℝ (fun i : {i // q (v i) ≠ 0} => q (v i)) := by
  let u (i : {i // q (v i) ≠ 0}) : V := v i
  have hr : range u = v '' {i | q (v i) ≠ 0} := by
    ext x
    simp [u]
  have hd : Disjoint (Submodule.span ℝ (range u)) q.ker := by
    rw [hr]
    have hs : Disjoint {i | q (v i) ≠ 0} {i | q (v i) = 0} :=
      Set.disjoint_left.mpr (fun _ hi hj => hi hj)
    exact (hv.disjoint_span_image hs).mono_right hk
  exact (q.linearIndependent_iff_of_disjoint hd).mpr (hv.comp _ Subtype.val_injective)

private theorem natCombination_injective {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] {v : ι → V} (hv : LinearIndependent ℝ v) :
    Function.Injective (fun n : ι → ℕ => ∑ i, n i • v i) := by
  intro n m h
  funext i
  have hi := (linearIndependent_iff'ₛ.mp hv) Finset.univ
    (fun j => (n j : ℝ)) (fun j => (m j : ℝ)) (by
      simpa only [Nat.cast_smul_eq_nsmul] using h) i (Finset.mem_univ i)
  exact_mod_cast hi

private theorem eq_coefficient_single' {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] {v : ι → V} (hv : LinearIndependent ℝ v)
    {n : ι → ℕ} {j : ι} (h : (∑ i, n i • v i) = v j) : n = Pi.single j 1 := by
  apply natCombination_injective hv
  change (∑ i, n i • v i) = ∑ i, (Pi.single j 1 : ι → ℕ) i • v i
  rw [h, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

private theorem exists_projected_natCombination {V W : Type*} [DecidableEq W]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {P : Finset V} {f : V →ₗ[ℝ] ℝ} (hpos : ∀ x ∈ P, 0 < f x) (q : V →ₗ[ℝ] W)
    {x : V} (hx : x ∈ P) :
    ∃ n : {i : indecomposable P // q (i : V) ≠ 0} → ℕ,
      q x = ∑ i, n i • q (i.val : V) := by
  obtain ⟨n, hn⟩ := exists_natCombination P f hpos hx
  refine ⟨fun i => n i.val, ?_⟩
  have hq := congrArg q hn
  simp only [map_sum, map_nsmul] at hq
  rw [hq, ← Fintype.sum_subtype_add_sum_subtype (fun i : indecomposable P => q (i : V) ≠ 0)
    (fun i => n i • q (i : V))]
  have hzero : (∑ i : {i : indecomposable P // ¬ q (i : V) ≠ 0}, n i.val • q (i.val : V)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [not_ne_iff.mp i.property, nsmul_zero]
  rw [hzero, add_zero]

private theorem indecomposable_image {V W : Type*} [DecidableEq W]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (P : Finset V) (f : V →ₗ[ℝ] ℝ) (hpos : ∀ x ∈ P, 0 < f x) (q : V →ₗ[ℝ] W)
    (hq : LinearIndependent ℝ (fun i : {i : indecomposable P // q (i : V) ≠ 0} => q (i.val : V))) :
    (↑(indecomposable ((P.image q).erase 0)) : Set W) =
      Set.range (fun i : {i : indecomposable P // q (i : V) ≠ 0} => q (i.val : V)) := by
  let Q := (P.image q).erase 0
  have hmem {x : V} (hx : x ∈ P) (hn : q x ≠ 0) : q x ∈ Q :=
    Finset.mem_erase.mpr ⟨hn, Finset.mem_image_of_mem _ hx⟩
  ext z
  constructor
  · intro hz
    obtain ⟨hn, hzi⟩ := Finset.mem_erase.mp (mem_indec.mp hz).1
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzi
    revert hz hn
    refine finite_positive_induction P f hpos
      (C := fun x => q x ∈ indecomposable Q → q x ≠ 0 →
        q x ∈ Set.range (fun i : {i : indecomposable P // q (i : V) ≠ 0} => q (i.val : V)))
      (fun x hx ih hz hn => ?_) x hx
    by_cases hs : x ∈ indecomposable P
    · exact ⟨⟨⟨x, hs⟩, hn⟩, rfl⟩
    · have hsplit : ∃ u ∈ P, ∃ w ∈ P, x = u + w := by
        by_contra hh
        exact hs (Finset.mem_filter.mpr ⟨hx, hh⟩)
      obtain ⟨u, hu, w, hw, he⟩ := hsplit
      have hqe : q x = q u + q w := by rw [he, map_add]
      have hrec := ih u hu w hw he
      by_cases hqu : q u = 0
      · have heq : q x = q w := by rw [hqe, hqu, zero_add]
        exact heq.symm ▸ hrec.2 (heq ▸ hz) (heq ▸ hn)
      by_cases hqw : q w = 0
      · have heq : q x = q u := by rw [hqe, hqw, add_zero]
        exact heq.symm ▸ hrec.1 (heq ▸ hz) (heq ▸ hn)
      exact False.elim ((mem_indec.mp hz).2 ⟨q u, hmem hu hqu, q w, hmem hw hqw, hqe⟩)
  · rintro ⟨i, rfl⟩
    refine mem_indec.mpr ⟨hmem (mem_indec.mp i.val.property).1 i.property, ?_⟩
    rintro ⟨u, hu, w, hw, heq⟩
    obtain ⟨hu0, hu'⟩ := Finset.mem_erase.mp hu
    obtain ⟨hw0, hw'⟩ := Finset.mem_erase.mp hw
    obtain ⟨u', hup, rfl⟩ := Finset.mem_image.mp hu'
    obtain ⟨w', hwp, rfl⟩ := Finset.mem_image.mp hw'
    obtain ⟨nu, hnu⟩ := exists_projected_natCombination hpos q hup
    obtain ⟨nw, hnw⟩ := exists_projected_natCombination hpos q hwp
    have hc : (fun j => nu j + nw j) = Pi.single i 1 := by
      apply eq_coefficient_single' hq
      change (∑ j, (nu j + nw j) • q (j.val : V)) = q (i.val : V)
      simp only [add_nsmul, Finset.sum_add_distrib]
      rw [← hnu, ← hnw]
      exact heq.symm
    have hzero (n : _ → ℕ) (hn : n i = 0) (hle : ∀ j, n j ≤ nu j + nw j) :
        ∑ j, n j • q (j.val : V) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hji : j = i
      · simp [hji, hn]
      · have hle' := hle j
        have hj := congrFun hc j
        rw [Pi.single_eq_of_ne hji] at hj
        simp [show n j = 0 by omega]
    have hi := congrFun hc i
    simp only [Pi.single_eq_same] at hi
    by_cases hni : nu i = 0
    · exact hu0 (hnu.trans (hzero nu hni (fun j => Nat.le_add_right _ _)))
    · exact hw0 (hnw.trans (hzero nw (by omega) (fun j => Nat.le_add_left _ _)))

private theorem mem_restrictedRoots_pos {R : Finset E} {a : Submodule ℝ E} {h : a}
    {x : E} (hx : x ∈ R) :
    restrictedRoot a x ∈ restrictedRoots a (posSet R h) ↔ 0 < ⟪restrictedRoot a x, h⟫ := by
  constructor
  · intro hr
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hr
    rw [← he, inner_restrictedRoot_subtype]
    exact (Finset.mem_filter.mp hy).2
  · intro hp
    rw [inner_restrictedRoot_subtype] at hp
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, hp⟩)

private theorem mem_simpleRoots_iff {a : Submodule ℝ E} {S : Finset E} {x : a} :
    x ∈ simpleRoots a S ↔ x ∈ restrictedRoots a S ∧
      ¬ ∃ u ∈ restrictedRoots a S, ∃ w ∈ restrictedRoots a S, x = u + w := Finset.mem_filter

private theorem inner_wall_pos {R : Finset E} {a : Submodule ℝ E} {h w : a} {v : a}
    (hh : IsRegular R a h)
    (hw : ∀ i : simpleRoots a (posSet R h), ⟪(i : a), w⟫ = if (i : a) = v then 0 else 1)
    {x : a} (hx : x ∈ restrictedRoots a (posSet R h)) (hn : x ∉ ℝ ∙ v) : 0 < ⟪x, w⟫ := by
  obtain ⟨n, he⟩ := exists_simpleRoot_combination (mem_parabolics_posSet hh) hx
  have hsum : ⟪x, w⟫ = ∑ i, (n i : ℝ) * (if (i : a) = v then 0 else 1) := by
    rw [he, sum_inner]
    simp only [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left, hw]
  have hnonneg (i : simpleRoots a (posSet R h)) :
      0 ≤ (n i : ℝ) * (if (i : a) = v then 0 else 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by split <;> norm_num)
  by_contra! hnpos
  have hz : ⟪x, w⟫ = 0 := le_antisymm hnpos (hsum ▸ Finset.sum_nonneg (fun i _ => hnonneg i))
  rw [hsum, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)] at hz
  apply hn
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  by_cases hi' : (i : a) = v
  · rw [hi']
    exact nsmul_mem (Submodule.mem_span_singleton_self v) _
  · have hni : n i = 0 := by simpa [hi'] using hz i hi
    simp [hni]

omit [FiniteDimensional ℝ E] in
private theorem inner_wall_zero {a : Submodule ℝ E} {v w x : a}
    (hw : ⟪v, w⟫ = 0) (hx : x ∈ ℝ ∙ v) : ⟪x, w⟫ = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [real_inner_smul_left, hw, mul_zero]

set_option maxHeartbeats 1200000 in
/-- Each simple root determines a chamber on the opposite side of its wall. -/
theorem exists_adjacentAlong {R : Finset E} {a : Submodule ℝ E} {S : Finset E} {v : a}
    (hR : IsRootSet R) (ha : IsLeviSpace R a) (hS : S ∈ parabolics R a)
    (hv : v ∈ simpleRoots a S) :
    ∃ S' ∈ parabolics R a, IsAdjacentAlong R a S S' v := by
  have hlin := linearIndependent_simpleRoots hR ha hS
  obtain ⟨_, ⟨h₀, hh, rfl⟩⟩ := Finset.mem_filter.mp hS
  let h : a := ⟨h₀, hh.1⟩
  let L : Submodule ℝ a := ℝ ∙ v
  obtain ⟨w, hw⟩ := exists_inner_values hlin (fun i => if (i : a) = v then 0 else 1)
  have hwv : ⟪v, w⟫ = 0 := by simpa using hw ⟨v, hv⟩
  let q : E → a := restrictedRoot a
  have hqneg (x : E) : q (-x) = -q x := a.orthogonalProjectionOnto.map_neg x
  have hsign (x : E) (hx : x ∈ R) (hn : q x ∉ L) : 0 < ⟪q x, h⟫ * ⟪q x, w⟫ := by
    have hne : q x ≠ 0 := fun he => hn (he ▸ L.zero_mem)
    have hne' : ⟪q x, h⟫ ≠ 0 := by
      rw [inner_restrictedRoot_subtype]
      exact hh.2 x hx hne
    rcases hne'.lt_or_gt with hneg | hpos
    · have hx' : -x ∈ R := hR.neg_mem hx
      have hn' : q (-x) ∉ L := by simpa only [hqneg, L.neg_mem_iff] using hn
      have hpos' : 0 < ⟪q (-x), h⟫ := by rw [hqneg, inner_neg_left]; linarith
      have hm := (mem_restrictedRoots_pos (a := a) (h := h) hx').mpr hpos'
      have hw' : 0 < ⟪q (-x), w⟫ :=
        inner_wall_pos (h := h) (w := w) (v := v) hh hw hm hn'
      rw [hqneg, inner_neg_left] at hw'
      exact mul_pos_of_neg_of_neg hneg (neg_pos.mp hw')
    · have hm := (mem_restrictedRoots_pos (a := a) (h := h) hx).mpr hpos
      exact mul_pos hpos (inner_wall_pos (h := h) (w := w) (v := v) hh hw hm hn)
  let U := ⋂ x ∈ R.filter (fun x => q x ∉ L), {t : ℝ | 0 < ⟪q x, h⟫ * ⟪q x, w - t • h⟫}
  have hU : IsOpen U := isOpen_biInter_finset (fun x _ =>
    isOpen_lt continuous_const (continuous_const.mul (continuous_const.inner
      (continuous_const.sub (continuous_id.smul continuous_const)))))
  have hzero : (0 : ℝ) ∈ U := by
    simp only [U, mem_iInter, Finset.mem_filter, mem_ofPred_eq, zero_smul, sub_zero]
    exact fun x hx => hsign x hx.1 hx.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 hzero
  let t := ε / 2
  have ht : 0 < t := half_pos hε
  have htU : t ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hε)
  let h' : a := w - t • h
  have hsame (x : E) (hx : x ∈ R) (hn : q x ∉ L) :
      0 < ⟪q x, h⟫ * ⟪q x, h'⟫ := by
    simp only [U, mem_iInter, Finset.mem_filter, mem_ofPred_eq] at htU
    exact htU x ⟨hx, hn⟩
  have hflip (x : a) (hx : x ∈ L) : ⟪x, h'⟫ = -(t * ⟪x, h⟫) := by
    rw [show h' = w - t • h from rfl, inner_sub_right, inner_wall_zero hwv hx,
      real_inner_smul_right, zero_sub]
  have hh' : IsRegular R a h' := by
    refine ⟨h'.property, fun x hx hn => ?_⟩
    rw [← inner_restrictedRoot_subtype a x h']
    by_cases hL : q x ∈ L
    · rw [hflip _ hL, neg_ne_zero, mul_ne_zero_iff]
      exact ⟨ht.ne', fun he => hh.2 x hx hn ((inner_restrictedRoot_subtype a x h).symm ▸ he)⟩
    · exact right_ne_zero_of_mul (hsame x hx hL).ne'
  refine ⟨posSet R h', mem_parabolics_posSet hh', hv, ?_, ?_⟩
  · obtain ⟨α, hα, hαv⟩ := Finset.mem_image.mp (mem_simpleRoots_iff.mp hv).1
    have hαR := (Finset.mem_filter.mp hα).1
    have hvp : 0 < ⟪v, h⟫ := simpleRoot_pos hv
    have hnv : -v ∈ L := L.neg_mem (Submodule.mem_span_singleton_self v)
    refine mem_simpleRoots_iff.mpr ⟨?_, ?_⟩
    · have he : q (-α) = -v := by rw [hqneg]; exact congrArg Neg.neg hαv
      rw [← he]
      apply (mem_restrictedRoots_pos (a := a) (h := h') (hR.neg_mem hαR)).mpr
      change 0 < ⟪q (-α), h'⟫
      rw [he, hflip _ hnv, inner_neg_left]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg ht (neg_neg_of_pos hvp))
    · have hwall (x : a) (hx : x ∈ restrictedRoots a (posSet R h')) :
          0 ≤ ⟪x, w⟫ ∧ (⟪x, w⟫ = 0 → -x ∈ restrictedRoots a (posSet R h)) := by
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hβR, hβ'⟩ := Finset.mem_filter.mp hβ
        have hβpos : 0 < ⟪q β, h'⟫ := (inner_restrictedRoot_subtype a β h').symm ▸ hβ'
        by_cases hb : q β ∈ L
        · refine ⟨(inner_wall_zero hwv hb).ge, fun _ => ?_⟩
          rw [← hqneg]
          apply (mem_restrictedRoots_pos (a := a) (h := h) (hR.neg_mem hβR)).mpr
          change 0 < ⟪q (-β), h⟫
          rw [hqneg, inner_neg_left]
          rw [hflip _ hb] at hβpos
          apply neg_pos.mpr
          by_contra! hn
          exact (not_lt_of_ge (mul_nonneg ht.le hn)) (neg_pos.mp hβpos)
        · have hβh : 0 < ⟪q β, h⟫ := pos_of_mul_pos_left (hsame β hβR hb) hβpos.le
          have hm := (mem_restrictedRoots_pos (a := a) (h := h) hβR).mpr hβh
          have hβw : 0 < ⟪q β, w⟫ := inner_wall_pos (h := h) (w := w) (v := v) hh hw hm hb
          exact ⟨hβw.le, fun hz => (hβw.ne' hz).elim⟩
      rintro ⟨x, hx, y, hy, he⟩
      have hp := hwall x hx
      have hq := hwall y hy
      have hz := inner_wall_zero hwv hnv
      rw [he, inner_add_left] at hz
      have hxS := hp.2 (by linarith [hp.1, hq.1])
      have hyS := hq.2 (by linarith [hp.1, hq.1])
      exact (mem_simpleRoots_iff.mp hv).2 ⟨-x, hxS, -y, hyS, by
        simpa only [neg_neg, neg_add] using congrArg Neg.neg he⟩
  · intro x hx hn
    have hL : q x ∉ L := fun hL => by
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hL
      exact hn r hr.symm
    have hprod := hsame x hx hL
    have hiff : 0 < ⟪q x, h⟫ ↔ 0 < ⟪q x, h'⟫ := by
      rcases mul_pos_iff.mp hprod with hp | hn
      · exact iff_of_true hp.1 hp.2
      · exact iff_of_false hn.1.not_gt hn.2.not_gt
    simpa only [posSet, Finset.mem_filter, hx, true_and, q, inner_restrictedRoot_subtype, h] using hiff

/-- Scalar multiples of a nonzero simple root occur at most once in a chamber's simple roots. -/
theorem simpleRoots_injOn_line {R : Finset E} {a : Submodule ℝ E} {S : Finset E}
    (hR : IsRootSet R) (ha : IsLeviSpace R a) (hS : S ∈ parabolics R a) :
    Set.InjOn (fun x : a => (ℝ ∙ x : Submodule ℝ a)) (simpleRoots a S : Set a) := by
  intro x hx y hy hxy
  obtain ⟨r, hr⟩ := Submodule.span_singleton_eq_span_singleton.mp hxy
  have hr' : (r : ℝ) • x = y := hr
  have h := (linearIndependent_simpleRoots hR ha hS).eq_of_smul_apply_eq_smul_apply
    (r : ℝ) 1 ⟨x, hx⟩ ⟨y, hy⟩ r.ne_zero (by simpa only [one_smul] using hr')
  exact congrArg Subtype.val h

private theorem linearIndependent_injective_mkQ {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    {v : ι → V} (hv : LinearIndependent ℝ v) (j : ι) :
    Function.Injective ((ℝ ∙ v j).mkQ ∘ v) := by
  intro i k hik
  by_contra hne
  have hm : v i - v k ∈ (ℝ ∙ v j) := by
    rw [← Submodule.ker_mkQ (ℝ ∙ v j), LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr hik
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
  by_cases hij : i = j
  · subst i
    have h := hv.eq_of_smul_apply_eq_smul_apply 1 (1 - r) k j one_ne_zero (by
      rw [one_smul, sub_smul, one_smul, hr]; abel)
    exact hne h.symm
  · have h := (linearIndependent_iff'.mp hv) {i, k, j}
      (fun a => (if a = i then 1 else 0) - (if a = k then 1 else 0) - (if a = j then r else 0))
    have hs : ∑ a ∈ ({i, k, j} : Finset ι),
        ((if a = i then 1 else 0) - (if a = k then 1 else 0) -
          (if a = j then r else 0)) • v a = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul]
      simp [Finset.sum_ite_eq', ← hr]
    have hi := h hs i (Finset.mem_insert_self ..)
    simp [hne, hij] at hi

private theorem projection_range_indec {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [DecidableEq W] {P : Finset V} {f : V →ₗ[ℝ] ℝ}
    (hpos : ∀ x ∈ P, 0 < f x) (q : V →ₗ[ℝ] W) (v : indecomposable P)
    (hlin : LinearIndependent ℝ (fun i : indecomposable P => (i : V)))
    (hker : q.ker = ℝ ∙ (v : V)) :
    Set.range (fun i : indecomposable P => q (i : V)) =
      insert 0 (↑(indecomposable ((P.image q).erase 0)) : Set W) := by
  have hv : q v = 0 := by
    change (v : V) ∈ q.ker
    rw [hker]
    exact Submodule.mem_span_singleton_self _
  have hi := linearIndependent_nonzero_map hlin q (by
    rw [hker, Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨v, hv, rfl⟩)
  rw [indecomposable_image P f hpos q hi]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    by_cases he : q i = 0
    · exact Or.inl he
    · exact Or.inr ⟨⟨i, he⟩, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨v, hv⟩
    · exact ⟨i.val, rfl⟩

private theorem restrictedRoots_pos {R : Finset E} {a : Submodule ℝ E} {h : a} {x : a}
    (hx : x ∈ restrictedRoots a (posSet R h)) : 0 < ⟪x, h⟫ := by
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hx
  rw [inner_restrictedRoot_subtype]
  exact (Finset.mem_filter.mp hxS).2

set_option maxHeartbeats 1000000 in
/-- Across a wall the simple roots match modulo its normal line. The wall root itself
is sent to its negative. -/
theorem exists_simpleRoots_equiv_of_adjacentAlong {R : Finset E} {a : Submodule ℝ E}
    {S T : Finset E} {v : a} (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hT : T ∈ parabolics R a) (hA : IsAdjacentAlong R a S T v) :
    ∃ e : simpleRoots a S ≃ simpleRoots a T,
      (e ⟨v, hA.1⟩ : a) = -v ∧ ∀ i, (e i : a) - (i : a) ∈ ℝ ∙ v := by
  have hlinS := linearIndependent_simpleRoots hR ha hS
  have hlinT := linearIndependent_simpleRoots hR ha hT
  let L : Submodule ℝ a := ℝ ∙ v
  let q := L.mkQ
  have hker : q.ker = L := L.ker_mkQ
  have hLneg : (ℝ ∙ (-v) : Submodule ℝ a) = L := by
    simpa only [neg_one_smul] using Submodule.span_singleton_smul_eq (isUnit_neg_one (α := ℝ)) v
  have hq0 (x : a) : q x = 0 ↔ x ∈ L := by rw [← LinearMap.mem_ker, hker]
  have hPT : ((restrictedRoots a S).image q).erase 0 = ((restrictedRoots a T).image q).erase 0 := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image]
    have hiff (α : E) (hα : α ∈ R) (hq : q (restrictedRoot a α) ≠ 0) : α ∈ S ↔ α ∈ T := by
      apply hA.2.2 α hα
      intro t ht
      exact hq ((hq0 _).mpr (Submodule.mem_span_singleton.mpr ⟨t, ht.symm⟩))
    have hSR : S ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hTR : T ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    constructor
    · rintro ⟨hn, y, hy, rfl⟩
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨hn, restrictedRoot a α, Finset.mem_image_of_mem _ ((hiff α (hSR hα) hn).mp hα), rfl⟩
    · rintro ⟨hn, y, hy, rfl⟩
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨hn, restrictedRoot a α, Finset.mem_image_of_mem _ ((hiff α (hTR hα) hn).mpr hα), rfl⟩
  let u (i : simpleRoots a S) := q (i : a)
  let w (i : simpleRoots a T) := q (i : a)
  have hu : Function.Injective u := linearIndependent_injective_mkQ hlinS ⟨v, hA.1⟩
  have hw : Function.Injective w := by
    have hh := linearIndependent_injective_mkQ hlinT ⟨-v, hA.2.1⟩
    change Function.Injective ((ℝ ∙ (-v) : Submodule ℝ a).mkQ ∘ fun i : simpleRoots a T => (i : a)) at hh
    rw [hLneg] at hh
    exact hh
  have hrange (B : Finset E) (hB : B ∈ parabolics R a) (z : a) (hz : z ∈ simpleRoots a B)
      (hzk : L = ℝ ∙ z) (hli : LinearIndependent ℝ (fun i : simpleRoots a B => (i : a))) :
      Set.range (fun i : simpleRoots a B => q (i : a)) =
        insert 0 (↑(indecomposable (((restrictedRoots a B).image q).erase 0)) : Set (a ⧸ L)) := by
    rw [simpleRoots_eq_indec] at hz hli ⊢
    obtain ⟨_, ⟨p, hp, rfl⟩⟩ := Finset.mem_filter.mp hB
    let p' : a := ⟨p, hp.1⟩
    refine projection_range_indec (f := innerₛₗ ℝ p') (fun x hx => ?_) q ⟨z, hz⟩ hli (hker.trans hzk)
    change 0 < ⟪p', x⟫
    rw [real_inner_comm]
    exact restrictedRoots_pos hx
  have heq : Set.range u = Set.range w := by
    rw [show Set.range u = _ from hrange S hS v hA.1 rfl hlinS,
      show Set.range w = _ from hrange T hT (-v) hA.2.1 hLneg.symm hlinT, hPT]
  let er : Set.range u ≃ Set.range w := Equiv.subtypeEquivRight (Set.ext_iff.mp heq)
  let e := (Equiv.ofInjective u hu).trans (er.trans (Equiv.ofInjective w hw).symm)
  have he (i : simpleRoots a S) : w (e i) = u i := by
    have h := (Equiv.ofInjective w hw).apply_symm_apply
      (er ((Equiv.ofInjective u hu) i))
    exact congrArg Subtype.val h
  refine ⟨e, ?_, fun i => ?_⟩
  · have hv0 := (hq0 v).mpr (Submodule.mem_span_singleton_self v)
    have hnv0 := (hq0 (-v)).mpr (L.neg_mem (Submodule.mem_span_singleton_self v))
    have hh : w (e ⟨v, hA.1⟩) = w ⟨-v, hA.2.1⟩ := (he _).trans (hv0.trans hnv0.symm)
    exact congrArg Subtype.val (hw hh)
  · apply (hq0 _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr (he i)

end Langlands.GMFamily
