/-
The compact-open subgroup argument adapts Mathlib/Topology/Algebra/OpenSubgroup.lean.
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the Mathlib file: Johan Commelin, Nailin Guan, Yi Song, Xuchun Li.
-/
import Langlands.Topology.LocallyProfiniteStatements
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Order.Disjointed

open Set Filter TopologicalSpace Topology
open scoped Pointwise

universe uX uI

namespace Langlands.Topology.LocallyProfiniteProof

section Groups

variable {G : Type uX} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compactness of the open set itself suffices for the uniform right-neighborhood argument. -/
private theorem compactOpenMulNhd {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) :
    ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply hWc.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, hmul⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans hmul⟩)
    fun U V ⟨T₁, hT₁, hmul₁⟩ ⟨T₂, hT₂, hmul₂⟩ ↦
      ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
        rw [union_mul]
        exact union_subset (mul_subset_mul_left inter_subset_left |>.trans hmul₁)
          (mul_subset_mul_left inter_subset_right |>.trans hmul₂)⟩
  intro x hxW
  have hx : (x, 1) ∈ (fun p : G × G ↦ p.1 * p.2) ⁻¹' W := by simp [hxW]
  obtain ⟨U, V, hUo, hVo, hxU, h1V, hUV⟩ :=
    isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWo) x 1 hx
  have hmul : U * V ⊆ W :=
    mul_subset_iff.mpr (fun _ ha _ hb ↦ hUV (mk_mem_prod ha hb))
  exact ⟨U ∩ W, ⟨U, hUo.mem_nhds hxU, W, fun _ ha ↦ ha, rfl⟩,
    V, hVo.mem_nhds h1V,
    fun _ ha ↦ hmul ((mul_subset_mul_right inter_subset_left) ha)⟩

/-- A compact open set containing the identity contains an open subgroup. -/
theorem openSubgroupInCompactOpen {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W)
    (h1W : 1 ∈ W) : ∃ H : OpenSubgroup G, (H : Set G) ⊆ W := by
  obtain ⟨T, hT, hWT⟩ := compactOpenMulNhd hWc hWo
  obtain ⟨U, hUT, hUo, h1U⟩ := mem_nhds_iff.mp hT
  let V : Set G := U ∩ U⁻¹
  have hVn : V ∈ 𝓝 (1 : G) := by
    simp [V, hUo.mem_nhds h1U, inv_mem_nhds_one]
  have hVi : V⁻¹ = V := by simp [V, inter_comm]
  have hVo : IsOpen V := hUo.inter hUo.inv
  have hWV : W * V ⊆ W :=
    (mul_subset_mul_left (inter_subset_left.trans hUT)).trans hWT
  let S : Subgroup G := {
    carrier := ⋃ n : ℕ, V ^ (n + 1)
    mul_mem' := fun ha hb ↦ by
      obtain ⟨k, hk⟩ := mem_iUnion.mp ha
      obtain ⟨l, hl⟩ := mem_iUnion.mp hb
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc, pow_add]
      exact Set.mul_mem_mul hk hl
    one_mem' := by
      apply mem_iUnion.mpr
      use 0
      simp [mem_of_mem_nhds hVn]
    inv_mem' := fun ha ↦ by
      obtain ⟨k, hk⟩ := mem_iUnion.mp ha
      apply mem_iUnion.mpr
      use k
      rw [← hVi]
      simpa only [inv_pow, Set.mem_inv, inv_inv] using hk }
  have hSo : IsOpen (⋃ n : ℕ, V ^ (n + 1)) := by
    refine isOpen_iUnion fun n ↦ ?_
    rw [pow_succ]
    exact hVo.mul_left
  refine ⟨⟨S, hSo⟩, ?_⟩
  have hp (n : ℕ) : W * V ^ (n + 1) ⊆ W := by
    induction n with
    | zero => simpa using hWV
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact (Set.mul_subset_mul_right ih).trans hWV
  have hsub (n : ℕ) : V ^ (n + 1) ⊆ W * V ^ (n + 1) := by
    intro x hx
    exact ⟨1, h1W, x, hx, one_mul x⟩
  exact iUnion_subset fun n ↦ (hsub n).trans (hp n)

end Groups

theorem vanDantzig : LocallyProfiniteStatements.VanDantzig.{uX} := by
  intro G _ _ _
  constructor
  · intro hG
    let : T2Space G := hG.t2Space
    refine ⟨hG.t2Space, fun U hU ↦ ?_⟩
    obtain ⟨W, h1W, hWo, hWc, hWU⟩ := hG.2 1 U hU
    obtain ⟨H, hHW⟩ := openSubgroupInCompactOpen hWc hWo h1W
    exact ⟨H, hWc.of_isClosed_subset H.isClosed hHW, hHW.trans hWU⟩
  · rintro ⟨hT2, hBasis⟩
    refine ⟨hT2, fun x U hU ↦ ?_⟩
    have hpre : (fun y : G ↦ x * y) ⁻¹' U ∈ 𝓝 (1 : G) := by
      have hc : Continuous (fun y : G ↦ x * y) :=
        continuous_const.mul continuous_id
      exact hc.continuousAt (by simpa only [mul_one] using hU)
    obtain ⟨H, hHc, hHU⟩ := hBasis _ hpre
    refine ⟨(fun y : G ↦ x * y) '' (H : Set G),
      ⟨1, H.one_mem, mul_one x⟩, isOpenMap_mul_left x _ H.isOpen,
      hHc.image (continuous_const.mul continuous_id), ?_⟩
    exact image_subset_iff.mpr hHU

theorem locallyClosedSubspaces : LocallyProfiniteStatements.LocallyClosedSubspaces.{uX} := by
  intro X _ hX Y hY
  let : T2Space X := hX.t2Space
  let : LocallyCompactSpace X := hX.locallyCompactSpace
  let : TotallyDisconnectedSpace X := hX.totallyDisconnectedSpace
  let : LocallyCompactSpace Y := hY.locallyCompactSpace
  exact isLocallyProfinite_of_mathlib

theorem finiteDisjointRefinement :
    LocallyProfiniteStatements.FiniteDisjointRefinement.{uX, uI} := by
  classical
  intro X _ hX K hK I U hU hKU
  let : T2Space X := hX.t2Space
  have hlocal (x : K) :
      ∃ V : Set X, x.val ∈ V ∧ IsOpen V ∧ IsCompact V ∧ ∃ i, V ⊆ U i := by
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hKU x.property)
    obtain ⟨V, hxV, hVo, hVc, hVU⟩ := hX.2 x.val (U i) ((hU i).mem_nhds hxi)
    exact ⟨V, hxV, hVo, hVc, i, hVU⟩
  choose V hxV hVo hVc hVU using hlocal
  have hKV : K ⊆ ⋃ x : K, V x :=
    fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover V hVo hKV
  let e := (Fintype.equivFin S).symm
  let W : Fin (Fintype.card S) → Set X := fun j ↦ V (e j).val
  have hW (j) : IsClopen (W j) := ⟨(hVc (e j).val).isClosed, hVo (e j).val⟩
  have hD (j) : IsClopen (disjointed W j) :=
    disjointedRec (fun {_ i} ht ↦ ht.diff (hW i)) (hW j)
  refine ⟨Fintype.card S, disjointed W,
    fun j ↦ ⟨(hD j).isOpen,
      (hVc (e j).val).of_isClosed_subset (hD j).isClosed (disjointed_le W j)⟩,
    disjoint_disjointed W, ?_, ?_⟩
  · rw [← iSup_eq_iUnion, iSup_disjointed, iSup_eq_iUnion]
    intro x hxK
    obtain ⟨s, hsS, hxVs⟩ := mem_iUnion₂.mp (hS hxK)
    exact mem_iUnion.mpr ⟨e.symm ⟨s, hsS⟩, by simpa [W] using hxVs⟩
  · intro j
    obtain ⟨i, hi⟩ := hVU (e j).val
    exact ⟨i, (disjointed_le W j).trans hi⟩

theorem denseOpenIntersections :
    LocallyProfiniteStatements.DenseOpenIntersections.{uX, uI} := by
  intro X _ hX I _ U hU hdU
  let : T2Space X := hX.t2Space
  let : LocallyCompactSpace X := hX.locallyCompactSpace
  exact dense_iInter_of_isOpen hU hdU

theorem locallyProfiniteAssertions :
    LocallyProfiniteStatements.LocallyProfiniteAssertions.{uX, uI} :=
  ⟨vanDantzig, locallyClosedSubspaces, finiteDisjointRefinement, denseOpenIntersections⟩

end Langlands.Topology.LocallyProfiniteProof
