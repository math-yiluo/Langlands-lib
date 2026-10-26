import Langlands.Representation.Induction.NormalCoinvariantKernelStatement
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Induction.CompactQuotientCutoff
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # The normal-coinvariant relation kernel of compact induction -/

noncomputable section

open Topology
open scoped Classical

namespace Langlands.Induction

universe uG uV

section General

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
variable (σ : Representation ℂ H V)

private def evaluation (g : G) : CompactFunctions H σ →ₗ[ℂ] V where
  toFun f := eval H σ f.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def cutoff (C : Set (LeftQuotient H)) (hc : IsCompact C) (hcl : IsClopen C) :
    CompactFunctions H σ →ₗ[ℂ] CompactFunctions H σ where
  toFun := compactQuotientCutoff H σ C hc hcl
  map_add' f k := by
    ext x
    change (if quotientMap H x ∈ C then eval H σ f.val x + eval H σ k.val x else 0) =
      (if quotientMap H x ∈ C then eval H σ f.val x else 0) +
        (if quotientMap H x ∈ C then eval H σ k.val x else 0)
    split_ifs <;> simp
  map_smul' c f := by
    ext x
    change (if quotientMap H x ∈ C then c • eval H σ f.val x else 0) =
      c • (if quotientMap H x ∈ C then eval H σ f.val x else 0)
    split_ifs <;> simp

private theorem cutoff_apply (C : Set (LeftQuotient H)) (hc : IsCompact C)
    (hcl : IsClopen C) (f : CompactFunctions H σ) (x : G) :
    eval H σ (cutoff H σ C hc hcl f).val x =
      if quotientMap H x ∈ C then eval H σ f.val x else 0 := rfl

include hNH in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem quotientMap_mul_normal (x : G) (n : N) :
    quotientMap H (x * (n : G)) = quotientMap H x := by
  symm
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  exact hNH (Subgroup.Normal.conj_mem inferInstance n.val n.property x)

include hNH in
private theorem evaluation_relation (n : N) (f : CompactFunctions H σ) (x : G) :
    evaluation H σ x (((compactInduced H σ).comp N.subtype) n f - f) ∈
      Representation.Coinvariants.ker (σ.comp (N.subgroupOf H).subtype) := by
  have hn : x * (n : G) * x⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem inferInstance n.val n.property x
  let p : N.subgroupOf H := ⟨⟨x * (n : G) * x⁻¹, hNH hn⟩, hn⟩
  have he : x * (n : G) = ((p.val : H) : G) * x := by
    dsimp [p]
    group
  change eval H σ f.val (x * (n : G)) - eval H σ f.val x ∈ _
  rw [he, eval_covariant H σ f.val p.val x]
  exact Representation.Coinvariants.sub_mem_ker p (eval H σ f.val x)

include hNH in
private theorem evaluation_mem (f : CompactFunctions H σ)
    (hf : f ∈ Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype))
    (x : G) :
    evaluation H σ x f ∈ Representation.Coinvariants.ker
      (σ.comp (N.subgroupOf H).subtype) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨n, k⟩, rfl⟩ := hf
    exact evaluation_relation H N hNH σ n k x
  | zero => simp
  | add f k hf hk ihf ihk =>
    simpa only [map_add] using (Representation.Coinvariants.ker
      (σ.comp (N.subgroupOf H).subtype)).add_mem ihf ihk
  | smul c f hf ih =>
    simpa only [map_smul] using (Representation.Coinvariants.ker
      (σ.comp (N.subgroupOf H).subtype)).smul_mem c ih

include hNH in
private theorem cutoff_mem (C : Set (LeftQuotient H)) (hc : IsCompact C)
    (hcl : IsClopen C) (f : CompactFunctions H σ)
    (hf : f ∈ Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype)) :
    cutoff H σ C hc hcl f ∈
      Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨n, k⟩, rfl⟩ := hf
    have heq : cutoff H σ C hc hcl (((compactInduced H σ).comp N.subtype) n k - k) =
        ((compactInduced H σ).comp N.subtype) n (cutoff H σ C hc hcl k) -
          cutoff H σ C hc hcl k := by
      ext x
      change (if quotientMap H x ∈ C then
        eval H σ k.val (x * (n : G)) - eval H σ k.val x else 0) =
        (if quotientMap H (x * (n : G)) ∈ C then
          eval H σ k.val (x * (n : G)) else 0) -
        (if quotientMap H x ∈ C then eval H σ k.val x else 0)
      rw [quotientMap_mul_normal H N hNH]
      split_ifs <;> simp
    rw [heq]
    exact Representation.Coinvariants.sub_mem_ker n _
  | zero => simp
  | add f k hf hk ihf ihk =>
    simpa only [map_add] using (Representation.Coinvariants.ker
      ((compactInduced H σ).comp N.subtype)).add_mem ihf ihk
  | smul c f hf ih =>
    simpa only [map_smul] using (Representation.Coinvariants.ker
      ((compactInduced H σ).comp N.subtype)).smul_mem c ih

end General

section Local

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable [NonarchimedeanGroup G] [LocallyCompactSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
variable (σ : Representation ℂ H V)

/-- Every coefficient relation lifts to a global relation with the chosen value. -/
private theorem exists_relation_evaluation (hσ : IsSmooth σ) (g : G) (v : V)
    (hv : v ∈ Representation.Coinvariants.ker (σ.comp (N.subgroupOf H).subtype)) :
    ∃ r : CompactFunctions H σ,
      r ∈ Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype) ∧
        evaluation H σ g r = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨p, w⟩, rfl⟩ := hv
    let s := compactLocalSection H σ hσ g w Set.univ isOpen_univ (Set.mem_univ _)
    have hs : eval H σ s.val g = w := compactLocalSection_apply H σ hσ g w
      Set.univ isOpen_univ (Set.mem_univ _)
    let n : N := ⟨g⁻¹ * ((p.val : H) : G) * g, by
      simpa using Subgroup.Normal.conj_mem inferInstance
        ((p.val : H) : G) p.property g⁻¹⟩
    refine ⟨((compactInduced H σ).comp N.subtype) n s - s,
      Representation.Coinvariants.sub_mem_ker n s, ?_⟩
    have he : g * (n : G) = ((p.val : H) : G) * g := by
      dsimp [n]
      group
    change eval H σ s.val (g * (n : G)) - eval H σ s.val g = _
    rw [he, eval_covariant H σ s.val p.val g, hs]
    rfl
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add v w hv hw ihv ihw =>
    obtain ⟨r, hr, hrv⟩ := ihv
    obtain ⟨s, hs, hsw⟩ := ihw
    exact ⟨r + s, Submodule.add_mem _ hr hs, by rw [map_add, hrv, hsw]⟩
  | smul c v hv ih =>
    obtain ⟨r, hr, hrv⟩ := ih
    exact ⟨c • r, Submodule.smul_mem _ c hr, by rw [map_smul, hrv]⟩

include hNH in
/-- A relation with the correct value gives a relation cutoff near that coset. -/
private theorem exists_local_relation_cutoff (hH : IsClosed (H : Set G))
    (hσ : IsSmooth σ) (f : CompactFunctions H σ) (g : G)
    (hg : eval H σ f.val g ∈
      Representation.Coinvariants.ker (σ.comp (N.subgroupOf H).subtype)) :
    ∃ (C : Set (LeftQuotient H)) (hc : IsCompact C) (hcl : IsClopen C),
      quotientMap H g ∈ C ∧ cutoff H σ C hc hcl f ∈
        Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype) := by
  obtain ⟨r, hr, hrg⟩ := exists_relation_evaluation H N σ hσ g _ hg
  let e := f - r
  have heg : eval H σ e.val g = 0 := by
    change eval H σ f.val g - eval H σ r.val g = 0
    exact sub_eq_zero.mpr hrg.symm
  have hgU : quotientMap H g ∈
      (quotientSupport H (eval H σ e.val))ᶜ := by
    intro hmem
    have hmem' : g ∈ quotientMap H ⁻¹' quotientSupport H (eval H σ e.val) := hmem
    rw [quotientMap_preimage_quotientSupport] at hmem'
    exact hmem' heg
  obtain ⟨C, hc, hcl, hgC, hCU⟩ :=
    exists_compactClopen_quotientNeighborhood H hH (quotientMap H g)
      (quotientSupport H (eval H σ e.val))ᶜ
      (isClosed_quotientSupport H σ e.val).isOpen_compl hgU
  have heq : cutoff H σ C hc hcl f = cutoff H σ C hc hcl r := by
    ext x
    change eval H σ (cutoff H σ C hc hcl f).val x =
      eval H σ (cutoff H σ C hc hcl r).val x
    rw [cutoff_apply, cutoff_apply]
    split_ifs with hx
    · have hezero : eval H σ e.val x = 0 := by
        by_contra hn
        exact hCU hx ⟨x, hn, rfl⟩
      exact sub_eq_zero.mp hezero
    · rfl
  refine ⟨C, hc, hcl, hgC, ?_⟩
  rw [heq]
  exact cutoff_mem H N hNH σ C hc hcl r hr

end Local

section Patching

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H : Subgroup G) (σ : Representation ℂ H V)

/-- Finite compactness globalizes membership in a quotient-cutoff-stable submodule. -/
private theorem mem_of_local_cutoffs
    (M : Submodule ℂ (CompactFunctions H σ))
    (hM : ∀ (C : Set (LeftQuotient H)) (hc : IsCompact C) (hcl : IsClopen C)
      (r : CompactFunctions H σ), r ∈ M → cutoff H σ C hc hcl r ∈ M)
    (f : CompactFunctions H σ)
    (hloc : ∀ y : LeftQuotient H,
      ∃ (C : Set (LeftQuotient H)) (hc : IsCompact C) (hcl : IsClopen C),
        y ∈ C ∧ cutoff H σ C hc hcl f ∈ M) : f ∈ M := by
  classical
  choose C hc hcl hyC hfC using hloc
  obtain ⟨s, hs⟩ := f.property.elim_finite_subcover C
    (fun y => (hcl y).isOpen) (by intro y _; exact Set.mem_iUnion.mpr ⟨y, hyC y⟩)
  have hct (t : Finset (LeftQuotient H)) : IsCompact (⋃ y ∈ t, C y) :=
    t.isCompact_biUnion (fun y _ => hc y)
  have hclt (t : Finset (LeftQuotient H)) : IsClopen (⋃ y ∈ t, C y) :=
    isClopen_biUnion_finset (fun y _ => hcl y)
  have hmem (t : Finset (LeftQuotient H)) :
      cutoff H σ (⋃ y ∈ t, C y) (hct t) (hclt t) f ∈ M := by
    induction t using Finset.induction_on with
    | empty =>
      have heq : cutoff H σ (⋃ y ∈ (∅ : Finset (LeftQuotient H)), C y)
          (hct ∅) (hclt ∅) f = 0 := by
        ext x
        change (if quotientMap H x ∈ ⋃ y ∈ (∅ : Finset (LeftQuotient H)), C y
          then eval H σ f.val x else 0) = 0
        simp
      rw [heq]
      exact M.zero_mem
    | @insert y t hyt ih =>
      have heq : cutoff H σ (⋃ z ∈ insert y t, C z) (hct _) (hclt _) f =
          cutoff H σ (C y) (hc y) (hcl y) f +
            cutoff H σ (⋃ z ∈ t, C z) (hct t) (hclt t) f -
              cutoff H σ (C y) (hc y) (hcl y)
                (cutoff H σ (⋃ z ∈ t, C z) (hct t) (hclt t) f) := by
        ext x
        change (if quotientMap H x ∈ ⋃ z ∈ insert y t, C z then eval H σ f.val x else 0) =
          (if quotientMap H x ∈ C y then eval H σ f.val x else 0) +
            (if quotientMap H x ∈ ⋃ z ∈ t, C z then eval H σ f.val x else 0) -
              (if quotientMap H x ∈ C y then
                (if quotientMap H x ∈ ⋃ z ∈ t, C z then eval H σ f.val x else 0) else 0)
        have hun : (⋃ z ∈ insert y t, C z) = C y ∪ ⋃ z ∈ t, C z := by
          ext z
          simp
        rw [hun, Set.mem_union]
        by_cases hx : quotientMap H x ∈ C y <;>
          by_cases ht : quotientMap H x ∈ ⋃ z ∈ t, C z <;>
            simp only [hx, ht, or_self, or_true, or_false,
              ite_true, ite_false, add_sub_cancel_right, add_zero, zero_add, sub_zero]
      rw [heq]
      exact M.sub_mem (M.add_mem (hfC y) ih) (hM _ _ _ _ ih)
  have heq : cutoff H σ (⋃ y ∈ s, C y) (hct s) (hclt s) f = f := by
    ext x
    change (if quotientMap H x ∈ ⋃ y ∈ s, C y then eval H σ f.val x else 0) =
      eval H σ f.val x
    by_cases hx : eval H σ f.val x = 0
    · simp [hx]
    · exact ite_eq_left (hs ⟨x, hx, rfl⟩)
  rw [← heq]
  exact hmem s

end Patching

/-- The unchanged normal-coinvariant relation-kernel statement. -/
theorem compactInductionNormalCoinvariantKernel :
    CompactInductionNormalCoinvariantKernel.{uG,uV} := by
  classical
  intro G _ _ _ _ hBasis H N _ hH _ hNH V _ _ σ hσ f
  let : NonarchimedeanGroup G := {
    is_nonarchimedean := by
      intro U hU
      obtain ⟨O, hOU, hO, h1O⟩ := mem_nhds_iff.mp hU
      obtain ⟨K, _, hKO⟩ := hBasis O hO h1O
      exact ⟨K, hKO.trans hOU⟩ }
  obtain ⟨K, hKc, _⟩ := hBasis Set.univ isOpen_univ (Set.mem_univ _)
  let : LocallyCompactSpace G :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (K.isOpen.mem_nhds K.one_mem)
  constructor
  · intro hf g
    exact evaluation_mem H N hNH σ f hf g
  · intro hf
    apply mem_of_local_cutoffs H σ
      (Representation.Coinvariants.ker ((compactInduced H σ).comp N.subtype))
      (cutoff_mem H N hNH σ) f
    intro y
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    exact exists_local_relation_cutoff H N hNH σ hH hσ f g (hf g)

end Langlands.Induction
