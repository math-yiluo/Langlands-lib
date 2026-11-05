import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellIntegration
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Products of a contracted subgroup through an open cell -/

noncomputable section

open Filter Topology

namespace Langlands.HarishChandraSchwartz

section OpenCellContraction

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- Hypotheses under which a subgroup `U'` splits as `(U ∩ U') (V ∩ U')` through the open cell
`P × V → Γ`, `(p, v) ↦ p v⁻¹`. Conjugation by powers of `a` contracts exactly `U'` and preserves
`P` and `V`. Every point of `P` is `m u` with `m ∈ M` and `u ∈ U`; conjugation by powers of `b`
contracts `U`, fixes `M` pointwise and preserves `U'`; `U'` is closed and meets `M` trivially. -/
structure IsOpenCellContraction (P V U U' M : Subgroup Γ) (a b : Γ) : Prop where
  isOpenEmbedding : IsOpenEmbedding (openCellMap (P := P) (V := V))
  unipotent_le : U ≤ P
  mem_normalizer_parabolic : a ∈ Subgroup.normalizer (P : Set Γ)
  mem_normalizer_opposite : a ∈ Subgroup.normalizer (V : Set Γ)
  tendsto_conj : ∀ x ∈ U', Tendsto (fun n : ℕ => a ^ n * x * (a ^ n)⁻¹) atTop (𝓝 1)
  mem_of_tendsto_conj : ∀ x : Γ,
    Tendsto (fun n : ℕ => a ^ n * x * (a ^ n)⁻¹) atTop (𝓝 1) → x ∈ U'
  exists_levi_mul : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ U, p = m * u
  tendsto_levi_conj : ∀ u ∈ U, Tendsto (fun n : ℕ => b ^ n * u * (b ^ n)⁻¹) atTop (𝓝 1)
  commute_levi : ∀ m ∈ M, Commute b m
  isClosed : IsClosed (U' : Set Γ)
  mem_normalizer_target : b ∈ Subgroup.normalizer (U' : Set Γ)
  eq_one_of_mem_levi : ∀ m ∈ M, m ∈ U' → m = 1

/-- The multiplication map `(U ∩ U') × (V ∩ U') → U'`, with both factors read as subgroups
of `U'`. -/
def subgroupProductMap (U V U' : Subgroup Γ) :
    (U.subgroupOf U') × (V.subgroupOf U') → U' :=
  fun p => (p.1 : U') * (p.2 : U')

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
@[simp] theorem coe_subgroupProductMap {U V U' : Subgroup Γ}
    (p : (U.subgroupOf U') × (V.subgroupOf U')) :
    (subgroupProductMap U V U' p : Γ) = ((p.1 : U') : Γ) * ((p.2 : U') : Γ) := rfl

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- Conjugation by an element of a normalizer, and by its inverse, preserves the subgroup. -/
theorem conj_mem_of_mem_normalizer {H : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) {x : Γ} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem inv_conj_mem_of_mem_normalizer {H : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) {x : Γ} (hx : x ∈ H) :
    g⁻¹ * x * g ∈ H := by
  have h := conj_mem_of_mem_normalizer (inv_mem hg) hx
  rwa [inv_inv] at h

namespace IsOpenCellContraction

variable {P V U U' M : Subgroup Γ} {a b : Γ} (hc : IsOpenCellContraction P V U U' M a b)
include hc

/-- **Existence of the product decomposition.** Every `x ∈ U'` is `h * k` with
`h ∈ U ∩ U'` and `k ∈ V ∩ U'`. -/
theorem exists_mul_eq {x : Γ} (hx : x ∈ U') :
    ∃ h ∈ U, h ∈ U' ∧ ∃ k ∈ V, k ∈ U' ∧ x = h * k := by
  -- Move a conjugate of `x` into the open cell.
  have hΩ : Set.range (openCellMap (P := P) (V := V)) ∈ 𝓝 (1 : Γ) := by
    refine hc.isOpenEmbedding.isOpen_range.mem_nhds ⟨(1, 1), ?_⟩
    simp [openCellMap]
  obtain ⟨N, q, hq⟩ := ((hc.tendsto_conj x hx).eventually_mem hΩ).exists
  have haN : a ^ N ∈ Subgroup.normalizer (P : Set Γ) := pow_mem hc.mem_normalizer_parabolic N
  have haN' : a ^ N ∈ Subgroup.normalizer (V : Set Γ) := pow_mem hc.mem_normalizer_opposite N
  set p₀ : Γ := (a ^ N)⁻¹ * (q.1 : Γ) * a ^ N with hp₀
  set v₀ : Γ := (a ^ N)⁻¹ * (q.2 : Γ) * a ^ N with hv₀
  have hp₀P : p₀ ∈ P := inv_conj_mem_of_mem_normalizer haN q.1.2
  have hv₀V : v₀ ∈ V := inv_conj_mem_of_mem_normalizer haN' q.2.2
  have hxpv : x = p₀ * v₀⁻¹ := by
    have hq' : (q.1 : Γ) * (q.2 : Γ)⁻¹ = a ^ N * x * (a ^ N)⁻¹ := hq
    rw [hp₀, hv₀]
    calc x = (a ^ N)⁻¹ * (a ^ N * x * (a ^ N)⁻¹) * a ^ N := by group
      _ = (a ^ N)⁻¹ * ((q.1 : Γ) * (q.2 : Γ)⁻¹) * a ^ N := by rw [hq']
      _ = _ := by group
  -- The cell coordinates of the conjugates of `x` converge to the identity.
  let f : ℕ → P × V := fun n =>
    (⟨a ^ n * p₀ * (a ^ n)⁻¹,
        conj_mem_of_mem_normalizer (pow_mem hc.mem_normalizer_parabolic n) hp₀P⟩,
      ⟨a ^ n * v₀ * (a ^ n)⁻¹,
        conj_mem_of_mem_normalizer (pow_mem hc.mem_normalizer_opposite n) hv₀V⟩)
  have hf : ∀ n, openCellMap (f n) = a ^ n * x * (a ^ n)⁻¹ := by
    intro n
    simp only [openCellMap, f, hxpv]
    group
  have hf1 : Tendsto f atTop (𝓝 1) := by
    rw [hc.isOpenEmbedding.isInducing.tendsto_nhds_iff]
    have h1 : openCellMap (P := P) (V := V) 1 = 1 := by simp [openCellMap]
    rw [h1]
    convert hc.tendsto_conj x hx using 1
    funext n
    exact hf n
  have hv₀U' : v₀ ∈ U' := by
    refine hc.mem_of_tendsto_conj v₀ ?_
    have h2 := ((continuous_subtype_val.comp continuous_snd).tendsto (1 : P × V)).comp hf1
    simpa [f, Function.comp_def] using h2
  have hp₀U' : p₀ ∈ U' := by
    have : p₀ = x * v₀ := by rw [hxpv]; group
    rw [this]
    exact mul_mem hx hv₀U'
  -- The Levi component of `p₀` lies in `U' ∩ M`, hence is trivial.
  obtain ⟨m, hm, u, hu, hmu⟩ := hc.exists_levi_mul p₀ hp₀P
  have hconj : ∀ n : ℕ, b ^ n * p₀ * (b ^ n)⁻¹ = m * (b ^ n * u * (b ^ n)⁻¹) := by
    intro n
    have hcomm : Commute (b ^ n) m := (hc.commute_levi m hm).pow_left n
    rw [hmu, ← mul_assoc (b ^ n), hcomm.eq]
    group
  have hlim : Tendsto (fun n : ℕ => b ^ n * p₀ * (b ^ n)⁻¹) atTop (𝓝 m) := by
    simp_rw [hconj]
    simpa using (hc.tendsto_levi_conj u hu).const_mul m
  have hmU' : m ∈ U' := by
    refine hc.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    exact conj_mem_of_mem_normalizer (pow_mem hc.mem_normalizer_target n) hp₀U'
  have hm1 : m = 1 := hc.eq_one_of_mem_levi m hm hmU'
  have hp₀U : p₀ ∈ U := by rw [hmu, hm1, one_mul]; exact hu
  exact ⟨p₀, hp₀U, hp₀U', v₀⁻¹, inv_mem hv₀V, inv_mem hv₀U', hxpv⟩

omit [IsTopologicalGroup Γ] in
/-- **Uniqueness of the product decomposition.** -/
theorem eq_of_mul_eq {h h' k k' : Γ} (hh : h ∈ U) (hh' : h' ∈ U) (hk : k ∈ V) (hk' : k' ∈ V)
    (heq : h * k = h' * k') : h = h' ∧ k = k' := by
  have hinj := hc.isOpenEmbedding.injective
    (a₁ := (⟨h, hc.unipotent_le hh⟩, ⟨k⁻¹, inv_mem hk⟩))
    (a₂ := (⟨h', hc.unipotent_le hh'⟩, ⟨k'⁻¹, inv_mem hk'⟩)) (by simpa [openCellMap] using heq)
  simp only [Prod.mk.injEq, Subtype.mk.injEq, inv_inj] at hinj
  exact hinj

/-- The multiplication map is a homeomorphism. -/
theorem isHomeomorph_subgroupProductMap : IsHomeomorph (subgroupProductMap U V U') := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `val ∘ productMap = openCellMap ∘ ψ` with `ψ` inducing.
    let ψ₁ : U.subgroupOf U' → P := fun x => ⟨(x : U'), hc.unipotent_le x.2⟩
    let ψ₂ : V.subgroupOf U' → V := fun x => ⟨((x : U') : Γ)⁻¹, inv_mem x.2⟩
    have hvP : IsInducing (Subtype.val : P → Γ) := IsInducing.subtypeVal
    have hvV : IsInducing (Subtype.val : V → Γ) := IsInducing.subtypeVal
    have hvU' : IsInducing (Subtype.val : U' → Γ) := IsInducing.subtypeVal
    have hvU : IsInducing (Subtype.val : U.subgroupOf U' → U') := IsInducing.subtypeVal
    have hvV' : IsInducing (Subtype.val : V.subgroupOf U' → U') := IsInducing.subtypeVal
    have hψ₁ : IsInducing ψ₁ := by
      rw [← hvP.of_comp_iff]
      exact hvU'.comp hvU
    have hψ₂ : IsInducing ψ₂ := by
      rw [← hvV.of_comp_iff]
      exact (Homeomorph.inv Γ).isInducing.comp (hvU'.comp hvV')
    have hcomp : Subtype.val ∘ subgroupProductMap U V U' =
        openCellMap (P := P) (V := V) ∘ Prod.map ψ₁ ψ₂ := by
      funext p
      simp [openCellMap, ψ₁, ψ₂, subgroupProductMap]
    rw [← hvU'.of_comp_iff, hcomp]
    exact hc.isOpenEmbedding.isInducing.comp (hψ₁.prodMap hψ₂)
  · intro p p' hpp
    have hpp' : ((p.1 : U') : Γ) * ((p.2 : U') : Γ) = ((p'.1 : U') : Γ) * ((p'.2 : U') : Γ) :=
      congrArg Subtype.val hpp
    obtain ⟨h1, h2⟩ := hc.eq_of_mul_eq p.1.2 p'.1.2 p.2.2 p'.2.2 hpp'
    exact Prod.ext (Subtype.ext (Subtype.ext h1)) (Subtype.ext (Subtype.ext h2))
  · intro x
    obtain ⟨h, hU, hU', k, hV, hkU', hx⟩ := hc.exists_mul_eq x.2
    exact ⟨(⟨⟨h, hU'⟩, hU⟩, ⟨⟨k, hkU'⟩, hV⟩), Subtype.ext hx.symm⟩

/-- The product homeomorphism `(U ∩ U') × (V ∩ U') ≃ₜ U'`, `(h, k) ↦ h k`. -/
def productHomeomorph : (U.subgroupOf U') × (V.subgroupOf U') ≃ₜ U' :=
  hc.isHomeomorph_subgroupProductMap.homeomorph

theorem productHomeomorph_apply (p : (U.subgroupOf U') × (V.subgroupOf U')) :
    hc.productHomeomorph p = (p.1 : U') * (p.2 : U') := rfl

end IsOpenCellContraction

end OpenCellContraction

end Langlands.HarishChandraSchwartz
