import Langlands.GroupScheme.Rational.OrderedProductAlgebra
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Finite subgroup collection with increasing commutator heights -/

noncomputable section

universe v

open scoped commutatorElement

namespace Langlands.GroupTheory.HeightCollection

open Langlands.GroupScheme.RelativeRoot.CentralExtension

private theorem prod_ofFn_single {G : Type v} [Group G] {n : ℕ}
    (m : Fin n) (z : G) :
    (List.ofFn fun i => if i = m then z else 1).prod = z := by
  induction n with
  | zero => exact Fin.elim0 m
  | succ n ih =>
      refine Fin.cases ?_ (fun m => ?_) m
      · simp [List.ofFn_succ]
      · simpa [List.ofFn_succ, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero m)] using ih m

/-- A finite subgroup family whose commutators strictly increase the two
heights admits ordered coordinates, provided the family generates the group. -/
theorem orderedProduct_surjective_of_iSup_eq_top {n : ℕ} :
    ∀ (G : Type v) [Group G] (H : Fin n → Subgroup G) (w : Fin n → ℕ),
      (∀ i j, ⁅H i, H j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), H k) →
      (⨆ i, H i) = ⊤ →
      Function.Surjective (orderedProduct (fun i => (H i).subtype)) := by
  classical
  suffices ∀ d : ℕ, ∀ (G : Type v) [Group G]
      (H : Fin n → Subgroup G) (w : Fin n → ℕ),
      (Finset.univ.filter fun i => H i ≠ ⊥).card = d →
      (∀ i j, ⁅H i, H j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), H k) →
      (⨆ i, H i) = ⊤ →
      Function.Surjective (orderedProduct (fun i => (H i).subtype)) from
    fun G _ H w hc hg => this _ G H w rfl hc hg
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro G _ H w hcard hc hg
      let s : Finset (Fin n) := Finset.univ.filter fun i => H i ≠ ⊥
      by_cases hs : s.Nonempty
      · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s w hs
        have hcomm (j : Fin n) : ⁅H j, H m⁆ = ⊥ := by
          apply le_bot_iff.mp
          refine (hc j m).trans (iSup_le fun k => iSup_le fun hk => ?_)
          by_cases hk' : H k = ⊥
          · exact hk'.le
          · have hkm := hmax k (by simp only [s, Finset.mem_filter,
                Finset.mem_univ, true_and]; exact hk')
            exact False.elim (not_lt_of_ge hkm (lt_of_le_of_lt (le_max_right _ _) hk))
        have hall : (⊤ : Subgroup G) ≤ Subgroup.centralizer (H m : Set G) := by
          rw [← hg]
          exact iSup_le fun j => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm j)
        have hcentral : H m ≤ Subgroup.center G :=
          Subgroup.centralizer_eq_top_iff_subset.mp (top_unique hall)
        let : (H m).Normal := Subgroup.normal_of_le_center hcentral
        let q : G →* G ⧸ H m := QuotientGroup.mk' (H m)
        let R : Fin n → Subgroup (G ⧸ H m) := fun i => (H i).map q
        have hR (i j : Fin n) :
            ⁅R i, R j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), R k := by
          simpa only [R, ← Subgroup.map_commutator, Subgroup.map_iSup] using
            Subgroup.map_mono (f := q) (hc i j)
        have hgR : (⨆ i, R i) = ⊤ := by
          rw [← Subgroup.map_iSup, hg]
          exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
        have hmR : R m = ⊥ := by
          apply (Subgroup.map_eq_bot_iff (H m)).mpr
          exact le_of_eq (QuotientGroup.ker_mk' (H m)).symm
        have hsub : (Finset.univ.filter fun i => R i ≠ ⊥) ⊆ s := by
          intro i hi
          have hi' : R i ≠ ⊥ := (Finset.mem_filter.mp hi).2
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hbot
          apply hi'
          simp only [R, hbot, Subgroup.map_bot]
        have hlt : (Finset.univ.filter fun i => R i ≠ ⊥).card < d := by
          rw [← hcard]
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
          intro heq
          have : m ∈ Finset.univ.filter fun i => R i ≠ ⊥ := heq ▸ hm
          exact (Finset.mem_filter.mp this).2 hmR
        have hsur := ih _ hlt (G ⧸ H m) R w rfl hR hgR
        intro g
        obtain ⟨r, hr⟩ := hsur (q g)
        choose x hx hxq using fun i => (r i).property
        let a : ∀ i, H i := fun i => ⟨x i, hx i⟩
        have ha : q (orderedProduct (fun i => (H i).subtype) a) = q g := by
          rw [orderedProduct, map_list_prod, List.map_ofFn]
          change (List.ofFn fun i => q (x i)).prod = q g
          simp_rw [hxq]
          exact hr
        let z := (orderedProduct (fun i => (H i).subtype) a)⁻¹ * g
        have hzq : q z = 1 := by simp only [z, map_mul, map_inv, ha, inv_mul_cancel]
        have hz : z ∈ H m := (QuotientGroup.eq_one_iff z).mp hzq
        let t : ∀ i, H i := fun i =>
          if h : i = m then ⟨z, h ▸ hz⟩ else 1
        have ht (i : Fin n) : ((t i : H i) : G) = if i = m then z else 1 := by
          simp only [t]
          split_ifs <;> rfl
        have htcentral (i : Fin n) (b : G) : Commute ((t i : H i) : G) b := by
          rw [ht]
          split_ifs
          · exact (Subgroup.mem_center_iff.mp (hcentral hz) b).symm
          · exact Commute.one_left b
        have htprod : orderedProduct (fun i => (H i).subtype) t = z := by
          simpa only [orderedProduct, Subgroup.subtype_apply, ht] using
            prod_ofFn_single m z
        refine ⟨fun i => a i * t i, ?_⟩
        rw [orderedProduct_mul_of_central _ a t htcentral, htprod]
        exact mul_inv_cancel_left _ _
      · have hbot (i : Fin n) : H i = ⊥ := by
          by_contra hi
          exact hs ⟨i, by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
        have htriv : (⊤ : Subgroup G) = ⊥ := by rw [← hg]; simp only [hbot, iSup_bot]
        intro g
        refine ⟨fun i => 1, ?_⟩
        have hg1 : g = 1 := (Subgroup.mem_bot.mp (htriv ▸ Subgroup.mem_top g))
        simp only [orderedProduct, map_one, List.ofFn_const,
          List.prod_replicate, one_pow, hg1]

/-- Increasing commutator heights make the ordered product exactly the subgroup
generated by the factors, with no choice of ordering imposed on the heights. -/
theorem range_orderedProduct_eq_iSup {G : Type v} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (w : Fin n → ℕ)
    (hc : ∀ i j, ⁅H i, H j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), H k) :
    Set.range (orderedProduct (fun i => (H i).subtype)) =
      ((⨆ i, H i : Subgroup G) : Set G) := by
  let K : Subgroup G := ⨆ i, H i
  let R : Fin n → Subgroup K := fun i => (H i).subgroupOf K
  have hmap (i : Fin n) : (R i).map K.subtype = H i :=
    Subgroup.map_subgroupOf_eq_of_le (le_iSup H i)
  have hR (i j : Fin n) :
      ⁅R i, R j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), R k := by
    apply (Subgroup.map_le_map_iff_of_injective K.subtype_injective).mp
    simpa only [Subgroup.map_commutator, Subgroup.map_iSup, hmap] using hc i j
  have hgR : (⨆ i, R i) = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    simp only [Subgroup.map_iSup, hmap, Subgroup.map_top, K.range_subtype]
    rfl
  have hsur := orderedProduct_surjective_of_iSup_eq_top K R w hR hgR
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    apply K.list_prod_mem
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact (le_iSup H i) (a i).property
  · intro hg
    obtain ⟨r, hr⟩ := hsur ⟨g, hg⟩
    let a : ∀ i, H i := fun i => ⟨((r i : R i) : K), (r i).property⟩
    refine ⟨a, ?_⟩
    simpa only [orderedProduct, map_list_prod, List.map_ofFn,
      Function.comp_def, Subgroup.subtype_apply, a] using
      congrArg K.subtype hr

/-- The subgroup whose carrier is the prescribed ordered product. -/
def orderedProductSubgroup {G : Type v} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (w : Fin n → ℕ)
    (hc : ∀ i j, ⁅H i, H j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), H k) :
    Subgroup G :=
  (⨆ i, H i).copy _ (range_orderedProduct_eq_iSup H w hc)

@[simp]
theorem mem_orderedProductSubgroup {G : Type v} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (w : Fin n → ℕ)
    (hc : ∀ i j, ⁅H i, H j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), H k)
    (g : G) :
    g ∈ orderedProductSubgroup H w hc ↔
      ∃ a, orderedProduct (fun i => (H i).subtype) a = g :=
  Iff.rfl

theorem orderedProductSubgroup_eq_iSup {G : Type v} [Group G] {n : ℕ}
    (H : Fin n → Subgroup G) (w : Fin n → ℕ)
    (hc : ∀ i j, ⁅H i, H j⁆ ≤ ⨆ k, ⨆ (_ : max (w i) (w j) < w k), H k) :
    orderedProductSubgroup H w hc = ⨆ i, H i :=
  Subgroup.copy_eq _ _ _

end Langlands.GroupTheory.HeightCollection
