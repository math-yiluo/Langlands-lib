import Langlands.Algebra.EnvelopingWeightDecomposition
import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Algebra.RelativeEnvelopingCenter

/-! # PBW coordinates of the positive right ideal -/

noncomputable section

universe u v w z

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

open Langlands.Archimedean.VermaPBW Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

section Subindices

variable {I : Type w} (p : I → Prop) [DecidablePred p]

/-- Retain the indices satisfying `p` in the same order, now as subtype
indices. -/
def orderedSubindices (l : List I) : List {a // p a} :=
  l.filterMap fun a => if ha : p a then some ⟨a, ha⟩ else none

@[simp]
theorem map_val_orderedSubindices (l : List I) :
    (orderedSubindices p l).map Subtype.val = l.filter (fun a => decide (p a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a <;> simpa [orderedSubindices, ha] using ih

theorem orderedSubindices_nodup {l : List I} (hl : l.Nodup) : (orderedSubindices p l).Nodup :=
  List.Nodup.of_map Subtype.val (by rw [map_val_orderedSubindices]; exact hl.filter _)

theorem mem_orderedSubindices {l : List I} (a : {a // p a}) (ha : a.val ∈ l) :
    a ∈ orderedSubindices p l := by
  exact List.mem_filterMap.mpr ⟨a.val, ha, dite_eq_left a.property⟩

theorem expand_orderedSubindices (l : List I) (β : {a // p a} →₀ ℕ) :
    (expand (orderedSubindices p l) β).map Subtype.val =
      expand l (β.embDomain (Function.Embedding.subtype p)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a
    · have hβ : (β.embDomain (Function.Embedding.subtype p)) a = β ⟨a, ha⟩ :=
        Finsupp.embDomain_apply_self (Function.Embedding.subtype p) β ⟨a, ha⟩
      simp only [orderedSubindices, List.filterMap_cons, dite_eq_left ha, expand, List.flatMap_cons,
        List.map_append, List.map_replicate, hβ]
      rw [← expand, ← expand, ← orderedSubindices, ih]
    · have han : a ∉ Set.range (Function.Embedding.subtype p) := by
        rintro ⟨x, rfl⟩
        exact ha x.property
      simp only [orderedSubindices, List.filterMap_cons, dite_eq_right ha, expand, List.flatMap_cons,
        Finsupp.embDomain_of_notMem_range _ _ _ han, List.replicate_zero, List.nil_append]
      exact ih

end Subindices

variable {k : Type u} [Field k] {L : Type v} [Ring L] [Algebra k L]
  {I : Type w} [Fintype I] [DecidableEq I]
  (b : Module.Basis I k L) (d : I → ℤ)

local notation "U" => UniversalEnvelopingAlgebra k L
local notation "ι" => UniversalEnvelopingAlgebra.ι k

section MappedBasis

variable {M : Type z} [LieRing M] [LieAlgebra k M]
  (p : I → Prop) [DecidablePred p] (j : M →ₗ⁅k⁆ L)
  (c : Module.Basis {a // p a} k M) (hc : ∀ a, j (c a) = b a.val)

omit [Fintype I] [DecidableEq I] in
include hc in
/-- The image of a monomial for a subset of the Lie basis has the same PBW
exponents extended by zero. -/
theorem map_orderedMonomial_subindices (l : List I) (β : {a // p a} →₀ ℕ) :
    Langlands.Algebra.LieEnvelopingEquiv.map j
        (orderedMonomial k M c (orderedSubindices p l) β) =
      orderedMonomial k L b l (β.embDomain (Function.Embedding.subtype p)) := by
  unfold orderedMonomial
  rw [map_word k M _ j.toLinearMap (Langlands.Algebra.LieEnvelopingEquiv.map_generator j)]
  rw [← expand_orderedSubindices p l β, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun a _ => hc a

end MappedBasis

section Coordinates

variable [CharZero k]

/-- The subspace spanned by ordered monomials having a positive letter. -/
def positivePBWSpan : Submodule k U :=
  Submodule.span k (weightOrderedPBWBasis b d ''
    {α | ∃ a, 0 < d a ∧ α a ≠ 0})

theorem positivePBWSpan_coord_zero {α : I →₀ ℕ} (hα : ∀ a, 0 < d a → α a = 0)
    {x : U} (hx : x ∈ positivePBWSpan b d) :
    (weightOrderedPBWBasis b d).repr x α = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, ⟨a, ha, hβ⟩, rfl⟩ := hx
    have hne : α ≠ β := fun h => hβ (h ▸ hα a ha)
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hne]
  | zero => rw [map_zero, Finsupp.zero_apply]
  | add x y _ _ h₁ h₂ => rw [map_add, Finsupp.add_apply, h₁, h₂, add_zero]
  | smul t x _ h => rw [map_smul, Finsupp.smul_apply, h, smul_zero]

omit [CharZero k] [Fintype I] [DecidableEq I] in
private theorem filter_positive_append_nonpositive (l : List I)
    (hl : l.Pairwise fun a a' => d a' ≤ d a) :
    l.filter (fun a => decide (0 < d a)) ++ l.filter (fun a => decide (¬ 0 < d a)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : 0 < d a
    · simpa [ha] using congrArg (List.cons a) (ih (List.pairwise_cons.mp hl).2)
    · have hnon (c : I) (hc : c ∈ a :: l) : ¬ 0 < d c := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha
        · exact fun h => ha (lt_of_lt_of_le h ((List.pairwise_cons.mp hl).1 c hc))
      have hp : (a :: l).filter (fun c => decide (0 < d c)) = [] :=
        List.filter_eq_nil_iff.mpr fun c hc => by simp [hnon c hc]
      have hm : (a :: l).filter (fun c => decide (¬ 0 < d c)) = a :: l :=
        List.filter_eq_self.mpr fun c hc => by simp [hnon c hc]
      rw [hp, hm, List.nil_append]

variable {N : Type z} [LieRing N] [LieAlgebra k N]
  (j : N →ₗ⁅k⁆ L) (c : Module.Basis {a : I // 0 < d a} k N)
  (hc : ∀ a, j (c a) = b a.val)

include hc in
private theorem positiveGenerator_mul_mem_positivePBWSpan (a : {a : I // 0 < d a}) (α : I →₀ ℕ) :
    ι (b a.val) * weightOrderedPBWBasis b d α ∈ positivePBWSpan b d := by
  classical
  let p (a : I) := 0 < d a
  let s := weightOrderedIndices d
  let pos := s.filter fun a => decide (p a)
  let rest := s.filter fun a => decide (¬p a)
  let sN := orderedSubindices p s
  let A := UniversalEnvelopingAlgebra k N
  let J := Langlands.Algebra.LieEnvelopingEquiv.map j
  let aug : A →ₐ[k] k := UniversalEnvelopingAlgebra.lift k (0 : N →ₗ⁅k⁆ k)
  let E := orderedMonomial k N c sN
  let e := Function.Embedding.subtype p
  let tail := word k L ((expand rest α).map b)
  let αN : {a // p a} →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => α a.val
  have hs : s = pos ++ rest :=
    (filter_positive_append_nonpositive d s (weightOrderedIndices_pairwise d)).symm
  have hsN : sN.Nodup := orderedSubindices_nodup p (weightOrderedIndices_nodup d)
  have hsNmem (a : {a // p a}) : a ∈ sN :=
    mem_orderedSubindices p a (mem_weightOrderedIndices d a.val)
  have hsplit (β : I →₀ ℕ) :
      expand s β = expand pos β ++ expand rest β :=
    (congrArg (fun t => expand t β) hs).trans (expand_append pos rest β)
  have hpos (a : I) (ha : a ∈ pos) : p a := by simpa only [pos, List.mem_filter,
    decide_eq_true_eq] using (List.mem_filter.mp ha).2
  have hneg (a : I) (ha : a ∈ rest) : ¬p a := by simpa only [rest, List.mem_filter,
    decide_eq_true_eq] using (List.mem_filter.mp ha).2
  have hzero (β : {a // p a} →₀ ℕ) (a : I) (ha : ¬p a) : β.embDomain e a = 0 :=
    Finsupp.embDomain_of_notMem_range _ _ _ (by
      rintro ⟨a', rfl⟩
      exact ha a'.property)
  have hmap (β : {a // p a} →₀ ℕ) :
      J (E β) = word k L ((expand pos (β.embDomain e)).map b) := by
    have hz : expand rest (β.embDomain e) = expand rest (0 : I →₀ ℕ) := by
      apply expand_congr
      intro a ha
      rw [hzero β a (hneg a ha), Finsupp.zero_apply]
    rw [show J (E β) = orderedMonomial k L b s (β.embDomain e) from
      map_orderedMonomial_subindices b p j c hc s β]
    unfold orderedMonomial
    rw [hsplit, hz, expand_zero, List.append_nil]
  have hmerge (β : {a // p a} →₀ ℕ) :
      J (E β) * tail =
        weightOrderedPBWBasis b d ((β.embDomain e) + α.filter (fun a => ¬p a)) := by
    let δ := β.embDomain e + α.filter (fun a => ¬p a)
    have hpos' : expand pos δ = expand pos (β.embDomain e) := by
      apply expand_congr
      intro a ha
      simp only [δ, Finsupp.add_apply, Finsupp.filter_apply,
        ite_eq_right (not_not_intro (hpos a ha)), add_zero]
    have hneg' : expand rest δ = expand rest α := by
      apply expand_congr
      intro a ha
      simp only [δ, Finsupp.add_apply, Finsupp.filter_apply, hzero β a (hneg a ha),
        ite_eq_left (hneg a ha), zero_add]
    rw [hmap, weightOrderedPBWBasis_apply]
    change _ = word k L ((expand s δ).map b)
    rw [hsplit, hpos', hneg', List.map_append, word_append]
  have hr : J (E αN) * tail = weightOrderedPBWBasis b d α := by
    have h : expand pos (αN.embDomain e) = expand pos α := by
      apply expand_congr
      intro a ha
      have he : e ⟨a, hpos a ha⟩ = a := rfl
      rw [← he, Finsupp.embDomain_apply_self]
      rfl
    rw [hmap, h, weightOrderedPBWBasis_apply]
    change _ = word k L ((expand s α).map b)
    rw [hsplit, List.map_append, word_append]
  have haug_ι (x : N) : aug (UniversalEnvelopingAlgebra.ι k x) = 0 :=
    UniversalEnvelopingAlgebra.lift_ι_apply k (0 : N →ₗ⁅k⁆ k) x
  have haug_word (l : List N) (hl : l ≠ []) : aug (word k N l) = 0 := by
    cases l with
    | nil => exact (hl rfl).elim
    | cons a l => rw [word_cons, map_mul, haug_ι, zero_mul]
  have htransform (u : A) : J u * tail - aug u • tail ∈ positivePBWSpan b d := by
    have hu : u ∈ Submodule.span k (Set.range E) :=
      top_le_span_orderedMonomial c hsN hsNmem Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨β, rfl⟩ := hu
      by_cases hβ : β = 0
      · subst β
        simp only [E, orderedMonomial, expand_zero, List.map_nil, word_nil, map_one,
          one_mul, one_smul, sub_self]
        exact (positivePBWSpan b d).zero_mem
      · obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hβ
        have hβa := Finsupp.mem_support_iff.mp ha
        have hex : (expand sN β).map c ≠ [] := by
          intro h
          have h' : expand sN β = [] := List.map_eq_nil_iff.mp h
          have hm : a ∈ expand sN β := List.mem_flatMap.mpr
            ⟨a, hsNmem a, List.mem_replicate.mpr ⟨hβa, rfl⟩⟩
          rw [h'] at hm
          exact List.not_mem_nil hm
        have haug : aug (E β) = 0 := haug_word _ hex
        rw [haug, zero_smul, sub_zero, hmerge]
        apply Submodule.subset_span
        refine ⟨_, ⟨a.val, a.property, ?_⟩, rfl⟩
        have hf : ¬¬p a.val := not_not_intro a.property
        rw [Finsupp.add_apply, Finsupp.filter_apply, ite_eq_right hf, add_zero]
        change (β.embDomain e) (e a) ≠ 0
        rwa [Finsupp.embDomain_apply_self]
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, map_add, add_mul, add_smul, add_sub_add_comm]
      exact (positivePBWSpan b d).add_mem hx hy
    | smul t x _ hx =>
      rw [map_smul, map_smul, smul_mul_assoc, smul_assoc, ← smul_sub]
      exact (positivePBWSpan b d).smul_mem t hx
  have h := htransform (UniversalEnvelopingAlgebra.ι k (c a) * E αN)
  rw [map_mul aug, haug_ι, zero_mul, zero_smul, sub_zero, map_mul,
    show J (UniversalEnvelopingAlgebra.ι k (c a)) = ι (b a.val) from
      (Langlands.Algebra.LieEnvelopingEquiv.map_generator j (c a)).trans
        (congrArg (UniversalEnvelopingAlgebra.ι k) (hc a)),
    mul_assoc, hr] at h
  exact h

include hc in
/-- The positive right ideal has zero coordinates on every PBW monomial
whose exponents in the positive directions all vanish. -/
theorem positiveWeightRightIdeal_le_positivePBWSpan :
    positiveWeightRightIdeal b d ≤ positivePBWSpan b d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, u, rfl⟩
  let B := weightOrderedPBWBasis b d
  rw [← B.linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [mul_smul_comm]
  exact Submodule.smul_mem _ _ (positiveGenerator_mul_mem_positivePBWSpan b d j c hc ⟨a, ha⟩ α)

end Coordinates

section ZeroWeight

variable [CharZero k] {M : Type z} [Ring M] [Algebra k M]
  (j : M →ₗ⁅k⁆ L) (c : Module.Basis {a : I // d a = 0} k M)
  (hc : ∀ a, j (c a) = b a.val)

include hc in
/-- A Levi enveloping element whose image has only positive PBW coordinates
is zero. -/
theorem eq_zero_of_envelopingMap_mem_positivePBWSpan (u : UniversalEnvelopingAlgebra k M)
    (hu : Langlands.Algebra.LieEnvelopingEquiv.map j u ∈ positivePBWSpan b d) :
    u = 0 := by
  let p (a : I) := d a = 0
  let s := weightOrderedIndices d
  let t := orderedSubindices p s
  let J := Langlands.Algebra.LieEnvelopingEquiv.map j
  let e := Function.Embedding.subtype p
  let BC := pbwBasis c (AssocSymbol.symbolData c) (AssocSymbol.symbolData_ξ_basis c)
    (orderedSubindices_nodup p (weightOrderedIndices_nodup d))
    (fun a => mem_orderedSubindices p a (mem_weightOrderedIndices d a.val))
  let B := weightOrderedPBWBasis b d
  have hmap (β : {a // p a} →₀ ℕ) : J (BC β) = B (β.embDomain e) := by
    change J (BC β) = weightOrderedPBWBasis b d (β.embDomain e)
    rw [weightOrderedPBWBasis_apply]
    change J (BC β) = orderedMonomial k L b s (β.embDomain e)
    rw [← map_orderedMonomial_subindices b p j c hc s β]
    congr 1
    exact pbwBasis_apply c (AssocSymbol.symbolData c) (AssocSymbol.symbolData_ξ_basis c)
      (orderedSubindices_nodup p (weightOrderedIndices_nodup d))
      (fun a => mem_orderedSubindices p a (mem_weightOrderedIndices d a.val)) β
  apply BC.repr.injective
  ext α
  have hα : B.coord (α.embDomain e) ∘ₗ J.toLinearMap = BC.coord α := by
    refine BC.ext fun β => ?_
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hmap, Module.Basis.coord_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Module.Basis.repr_self]
    by_cases h : α = β
    · subst β
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne ((Finsupp.embDomain_injective e).ne h),
        Finsupp.single_eq_of_ne h]
  have hcoord : B.repr (J u) (α.embDomain e) = BC.repr u α := LinearMap.congr_fun hα u
  rw [map_zero, Finsupp.zero_apply, ← hcoord]
  refine positivePBWSpan_coord_zero b d (fun a ha => ?_) hu
  exact Finsupp.embDomain_of_notMem_range _ _ _ (by
    rintro ⟨a', rfl⟩
    exact (ne_of_gt ha) a'.property)

end ZeroWeight

section Stability

variable {M : Type z} [LieRing M] [LieAlgebra k M]
  (j : M →ₗ⁅k⁆ L)
  (hbr : ∀ x (a : I), 0 < d a →
    ⁅j x, b a⁆ ∈ Submodule.span k (b '' {a | 0 < d a}))

omit [Fintype I] [DecidableEq I] in
private theorem mul_mem_positiveWeightRightIdeal_of_span
    {x : L} (hx : x ∈ Submodule.span k (b '' {a | 0 < d a})) (u : U) :
    ι x * u ∈ positiveWeightRightIdeal b d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨a, ha, u, rfl⟩
  | zero => rw [map_zero, zero_mul]; exact (positiveWeightRightIdeal b d).zero_mem
  | add x y _ _ hx hy => rw [map_add, add_mul]; exact (positiveWeightRightIdeal b d).add_mem hx hy
  | smul t x _ hx => rw [map_smul, smul_mul_assoc]; exact (positiveWeightRightIdeal b d).smul_mem t hx

omit [Fintype I] [DecidableEq I] in
include hbr in
private theorem positiveWeightRightIdeal_stable_generator (x : M) {u : U}
    (hu : u ∈ positiveWeightRightIdeal b d) :
    ι (j x) * u ∈ positiveWeightRightIdeal b d := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, v, rfl⟩ := hu
    have h1 := (UniversalEnvelopingAlgebra.ι k (L := L)).map_lie (j x) (b a)
    have h2 : ι (j x) * (ι (b a) * v) =
        ι (b a) * (ι (j x) * v) + ι ⁅j x, b a⁆ * v := by
      rw [h1, Ring.lie_def]
      noncomm_ring
    rw [h2]
    exact (positiveWeightRightIdeal b d).add_mem
      (Submodule.subset_span ⟨a, ha, _, rfl⟩)
      (mul_mem_positiveWeightRightIdeal_of_span b d (hbr x a ha) v)
  | zero => rw [mul_zero]; exact (positiveWeightRightIdeal b d).zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact (positiveWeightRightIdeal b d).add_mem hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact (positiveWeightRightIdeal b d).smul_mem t hx

omit [Fintype I] [DecidableEq I] in
include hbr in
/-- Stability of the positive generators under Levi brackets gives stability
of the right ideal under left multiplication by every Levi operator. -/
theorem positiveWeightRightIdeal_stable_enveloping (a : UniversalEnvelopingAlgebra k M)
    (u : U) (hu : u ∈ positiveWeightRightIdeal b d) :
    Langlands.Algebra.LieEnvelopingEquiv.map j a * u ∈ positiveWeightRightIdeal b d := by
  let J := Langlands.Algebra.LieEnvelopingEquiv.map j
  obtain ⟨N, hN⟩ := exists_mem_degreeFiltration k M a
  have ha := degreeFiltration_le_wordSpan k M N hN
  clear hN
  revert u
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    clear hl
    induction l with
    | nil =>
      intro u hu
      simpa only [word_nil, map_one, one_mul] using hu
    | cons x l ih =>
      intro u hu
      rw [word_cons, map_mul, mul_assoc, Langlands.Algebra.LieEnvelopingEquiv.map_generator]
      exact positiveWeightRightIdeal_stable_generator b d j hbr x (ih u hu)
  | zero => intro u _; rw [map_zero, zero_mul]; exact (positiveWeightRightIdeal b d).zero_mem
  | add x y _ _ hx hy =>
    intro u hu
    rw [map_add, add_mul]
    exact (positiveWeightRightIdeal b d).add_mem (hx _ hu) (hy _ hu)
  | smul t x _ hx =>
    intro u hu
    rw [map_smul, smul_mul_assoc]
    exact (positiveWeightRightIdeal b d).smul_mem t (hx _ hu)

end Stability

section Decomposition

variable [CharZero k] {M N : Type z} [Ring M] [Algebra k M] [LieRing N] [LieAlgebra k N]
  (j : M →ₗ⁅k⁆ L) (jN : N →ₗ⁅k⁆ L)
  (b₀ : Module.Basis {a : I // d a = 0} k M) (bN : Module.Basis {a : I // 0 < d a} k N)
  (h₀ : ∀ a, j (b₀ a) = b a.val) (hN : ∀ a, jN (bN a) = b a.val)
  (H : L) (hH : ∀ a, ⁅H, b a⁆ = (d a : k) • b a)

omit [Fintype I] in
include h₀ hH in
private theorem bracket_mem_positiveSpan (x : M) (a : I) (ha : 0 < d a) :
    ⁅j x, b a⁆ ∈ Submodule.span k (b '' {a | 0 < d a}) := by
  let ad : L →ₗ[k] L :=
    { toFun := fun X => ⁅H, X⁆
      map_add' := fun X Y => lie_add H X Y
      map_smul' := fun t X => lie_smul t H X }
  have hJ : ad ∘ₗ j.toLinearMap = 0 := by
    refine b₀.ext fun q => ?_
    change ⁅H, j (b₀ q)⁆ = 0
    rw [h₀, hH, q.property, Int.cast_zero, zero_smul]
  have hX : ⁅H, j x⁆ = 0 := LinearMap.congr_fun hJ x
  let y := ⁅j x, b a⁆
  have hY : ad y = (d a : k) • y := by
    change ⁅H, ⁅j x, b a⁆⁆ = _
    rw [leibniz_lie, hX, zero_lie, zero_add, hH]
    exact lie_smul (d a : k) (j x) (b a)
  have hcoord (q : I) : b.coord q ∘ₗ ad = (d q : k) • b.coord q := by
    refine b.ext fun t => ?_
    change b.coord q ⁅H, b t⁆ = (d q : k) • b.coord q (b t)
    rw [hH, map_smul]
    by_cases hqt : q = t
    · rw [hqt]
    · simp [Module.Basis.coord_apply, Module.Basis.repr_self, hqt]
  have hs (q : I) (hq : q ∈ (b.repr y).support) : 0 < d q := by
    have h : (d q : k) • b.repr y q = b.repr (ad y) q :=
      (LinearMap.congr_fun (hcoord q) y).symm
    rw [hY, map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul] at h
    have hv : (d q : k) = (d a : k) :=
      mul_right_cancel₀ (Finsupp.mem_support_iff.mp hq) h
    have hd : d q = d a := Int.cast_injective hv
    rwa [hd]
  change y ∈ _
  rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun q hq =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hs q hq, rfl⟩)

include h₀ hN hH in
/-- The positive and zero parts of an integral adjoint grading give the
triangular decomposition needed for the relative centre projection. -/
def relativeEnvelopingDecomposition_of_weight :
    RelativeEnvelopingDecomposition (Langlands.Algebra.LieEnvelopingEquiv.map j) where
  ideal := positiveWeightRightIdeal b d
  mul_mem_right _ hx y := mul_mem_positiveWeightRightIdeal b d hx y
  levi_mul_mem a u hu := positiveWeightRightIdeal_stable_enveloping b d j
    (bracket_mem_positiveSpan b d j b₀ h₀ H hH) a u hu
  eq_zero_of_mem a ha := eq_zero_of_envelopingMap_mem_positivePBWSpan b d j b₀ h₀ a
    (positiveWeightRightIdeal_le_positivePBWSpan b d jN bN hN ha)
  exists_representative z := by
    let J := Langlands.Algebra.LieEnvelopingEquiv.map j
    have hr : zeroWeightEnvelopingSubalgebra b d ≤ J.range := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨UniversalEnvelopingAlgebra.ι k (b₀ ⟨a, ha⟩),
        (Langlands.Algebra.LieEnvelopingEquiv.map_generator j _).trans
          (congrArg (UniversalEnvelopingAlgebra.ι k) (h₀ ⟨a, ha⟩))⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
      (center_mem_positiveWeight_sup_zeroWeight b d H hH z)
    obtain ⟨a, ha⟩ := hr hy
    refine ⟨a, ?_⟩
    change J a = y at ha
    change z.val - J a ∈ _
    rw [ha, ← hxy, add_sub_cancel_right]
    exact hx

end Decomposition

end Langlands.Algebra.UniversalEnveloping
