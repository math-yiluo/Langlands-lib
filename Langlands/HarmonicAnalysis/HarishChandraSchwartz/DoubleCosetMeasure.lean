import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Index

/-! # Measures of double cosets (Waldspurger I.1 (5))

Waldspurger 2003, I.1 (5): `C₁ δ₀(m)⁻¹ ≤ mes(K m K) ≤ C₂ δ₀(m)⁻¹` for `m ∈ M̄₀⁺`. The proof
compares `K m K` with `H m H` for a compact open `H ⊆ K`, uses
`mes(H m H) = mes(H) [H : m H m⁻¹ ∩ H]`, and computes the index through the factorization of
`H`, the unipotent factor being `δ₀(m)⁻¹` times a bounded index. This module proves, for a
group with a left invariant measure, the measure formulas for cosets and double cosets, the
comparison between `H` and `K`, the modulus identity for the index of a subgroup in its
conjugate, and the resulting two-sided bound from bounds on `[H : H ∩ m H m⁻¹]`.
-/

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

section Conj

variable {G : Type u} [Group G]

/-- The index `[H : H ∩ g H g⁻¹]`, the number of left cosets of `H` in `H g H` (Waldspurger's
`[H : mHm⁻¹ ∩ H]` in the proof of I.1 (5)); it is `0` when the index is infinite. -/
def doubleCosetIndex (H : Subgroup G) (g : G) : ℕ :=
  (conjSubgroup g H).relIndex H

theorem conjSubgroup_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjSubgroup g H ≤ conjSubgroup g K :=
  Subgroup.comap_mono h

/-- Left translates of a subgroup `Z` by elements of a finite family are pairwise disjoint as
soon as they are pairwise distinct. -/
theorem pairwise_disjoint_smul_of_injective {ι : Type*} (Z : Subgroup G) (a : ι → G)
    (ha : ∀ i j, a i • (Z : Set G) = a j • (Z : Set G) → i = j) :
    Pairwise (Function.onFun Disjoint fun i => a i • (Z : Set G)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hx hx' => hij (ha i j ?_)
  rw [mem_leftCoset_iff] at hx hx'
  rw [leftCoset_eq_iff (s := Z)]
  have h := Z.mul_mem hx (Z.inv_mem hx')
  simpa [mul_assoc] using h

/-- Two translates `(h₁ g) H` and `(h₂ g) H` with `h₁, h₂ ∈ H` coincide exactly when `h₁` and
`h₂` have the same class modulo `H ∩ g H g⁻¹`. -/
theorem translate_smul_eq_iff (H : Subgroup G) (g : G) (h₁ h₂ : H) :
    ((h₁ : G) * g) • (H : Set G) = ((h₂ : G) * g) • (H : Set G) ↔
      (QuotientGroup.mk h₁ : H ⧸ (conjSubgroup g H).subgroupOf H) = QuotientGroup.mk h₂ := by
  rw [leftCoset_eq_iff (s := H), QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, mul_assoc]

/-- `H g H = ⋃ (q g) H`, over representatives `q` of `H / (H ∩ g H g⁻¹)`. -/
theorem doubleCoset_eq_iUnion (H : Subgroup G) (g : G) :
    DoubleCoset.doubleCoset g H H =
      ⋃ q : H ⧸ (conjSubgroup g H).subgroupOf H, ((q.out : G) * g) • (H : Set G) := by
  rw [← DoubleCoset.doubleCoset_union_leftCoset]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨QuotientGroup.mk h, ?_⟩
    rwa [(translate_smul_eq_iff H g (QuotientGroup.mk h : H ⧸ _).out h).mpr
      (QuotientGroup.out_eq' _)]
  · rintro ⟨q, hx⟩
    exact ⟨q.out, hx⟩

/-- For `Z ≤ Y`, `Y = ⋃ q Z` over representatives `q` of `Y / Z`. -/
theorem coe_eq_iUnion_smul {Z Y : Subgroup G} (hZY : Z ≤ Y) :
    (Y : Set G) = ⋃ q : Y ⧸ Z.subgroupOf Y, ((q.out : Y) : G) • (Z : Set G) := by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hx
    refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (Z.subgroupOf Y) (⟨x, hx⟩ : Y)
    rw [mem_leftCoset_iff, hl]
    have hl' : ((l : Y) : G) ∈ Z := l.2
    simpa [mul_assoc] using Z.inv_mem hl'
  · rintro ⟨q, hx⟩
    rw [mem_leftCoset_iff] at hx
    have h := Y.mul_mem (q.out : Y).2 (hZY hx)
    simpa using h

theorem leftCoset_eq_iff_mk {Z Y : Subgroup G} (y₁ y₂ : Y) :
    (y₁ : G) • (Z : Set G) = (y₂ : G) • (Z : Set G) ↔
      (QuotientGroup.mk y₁ : Y ⧸ Z.subgroupOf Y) = QuotientGroup.mk y₂ := by
  rw [leftCoset_eq_iff (s := Z), QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

end Conj

section Measure

variable {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
  [μ.IsMulLeftInvariant]

/-- A union of finitely many distinct left translates of a measurable subgroup `Z` has
measure `(number of translates) · μ(Z)`. -/
theorem measure_iUnion_smul {ι : Type*} [Fintype ι] {Z : Subgroup G}
    (hZ : MeasurableSet (Z : Set G)) (a : ι → G)
    (ha : ∀ i j, a i • (Z : Set G) = a j • (Z : Set G) → i = j) :
    μ (⋃ i, a i • (Z : Set G)) = (Fintype.card ι : ℝ≥0∞) * μ Z := by
  rw [measure_iUnion (pairwise_disjoint_smul_of_injective Z a ha) fun _ => hZ.const_smul _]
  simp only [measure_smul]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- For measurable `Z ≤ Y` of finite index: `μ(Y) = [Y : Z] μ(Z)`. -/
theorem measure_eq_relIndex_mul {Z Y : Subgroup G} (hZY : Z ≤ Y)
    (hZ : MeasurableSet (Z : Set G)) (hfin : Z.relIndex Y ≠ 0) :
    μ Y = (Z.relIndex Y : ℝ≥0∞) * μ Z := by
  have : (Z.subgroupOf Y).FiniteIndex := ⟨hfin⟩
  let : Fintype (Y ⧸ Z.subgroupOf Y) := Fintype.ofFinite _
  rw [coe_eq_iUnion_smul hZY, measure_iUnion_smul μ hZ _ fun q q' h => by
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (leftCoset_eq_iff_mk _ _).mp h]
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/-- `μ(H g H) = [H : H ∩ g H g⁻¹] μ(H)` (Waldspurger's `mes(HmH) = mes(H) [H : mHm⁻¹ ∩ H]`
in the proof of I.1 (5)). -/
theorem measure_doubleCoset (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (g : G)
    (hfin : doubleCosetIndex H g ≠ 0) :
    μ (DoubleCoset.doubleCoset g H H) = (doubleCosetIndex H g : ℝ≥0∞) * μ H := by
  unfold doubleCosetIndex at *
  have : ((conjSubgroup g H).subgroupOf H).FiniteIndex := ⟨hfin⟩
  let : Fintype (H ⧸ (conjSubgroup g H).subgroupOf H) := Fintype.ofFinite _
  rw [doubleCoset_eq_iUnion, measure_iUnion_smul μ hH _ fun q q' h => by
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (translate_smul_eq_iff H g _ _).mp h]
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

omit [MeasurableSpace G] [MeasurableMul G] in
theorem doubleCoset_mono {H K : Subgroup G} (hHK : H ≤ K) (g : G) :
    DoubleCoset.doubleCoset g H H ⊆ DoubleCoset.doubleCoset g K K := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  exact DoubleCoset.mem_doubleCoset.mpr ⟨a, hHK ha, b, hHK hb, rfl⟩

omit [MeasurableSpace G] [MeasurableMul G] in
/-- Index comparison for `H ≤ K`: `[K : K ∩ g K g⁻¹] ≤ [H : H ∩ g H g⁻¹] [K : H]`. -/
theorem doubleCosetIndex_le {H K : Subgroup G} (hHK : H ≤ K) (g : G)
    (hHfin : doubleCosetIndex H g ≠ 0) (hKH : H.relIndex K ≠ 0) :
    doubleCosetIndex K g ≠ 0 ∧
      doubleCosetIndex K g ≤ doubleCosetIndex H g * H.relIndex K := by
  unfold doubleCosetIndex at *
  set B := conjSubgroup g H ⊓ H
  have hB : B.relIndex K = (conjSubgroup g H).relIndex H * H.relIndex K := by
    rw [← Subgroup.relIndex_mul_relIndex B H K inf_le_right hHK, Subgroup.inf_relIndex_right]
  have hBne : B.relIndex K ≠ 0 := by rw [hB]; exact mul_ne_zero hHfin hKH
  have hBA : B ≤ conjSubgroup g K ⊓ K :=
    inf_le_inf (conjSubgroup_mono g hHK) hHK
  rw [← Subgroup.inf_relIndex_right (conjSubgroup g K) K, ← hB]
  exact ⟨ne_zero_of_dvd_ne_zero hBne (Subgroup.relIndex_dvd_of_le_left K hBA),
    Subgroup.relIndex_le_of_le_left hBA hBne⟩

/-- The comparison of `H g H` and `K g K` for measurable `H ≤ K`, `[K : H] < ∞` and
`[H : H ∩ g H g⁻¹] < ∞`: `[H : H ∩ g H g⁻¹] μ(H) ≤ μ(K g K) ≤ [H : H ∩ g H g⁻¹] [K : H] μ(K)`. -/
theorem measure_doubleCoset_bounds {H K : Subgroup G} (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (g : G)
    (hHfin : doubleCosetIndex H g ≠ 0) (hKH : H.relIndex K ≠ 0) :
    (doubleCosetIndex H g : ℝ≥0∞) * μ H ≤ μ (DoubleCoset.doubleCoset g K K) ∧
      μ (DoubleCoset.doubleCoset g K K) ≤
        (doubleCosetIndex H g : ℝ≥0∞) * H.relIndex K * μ K := by
  obtain ⟨hKfin, hle⟩ := doubleCosetIndex_le hHK g hHfin hKH
  refine ⟨?_, ?_⟩
  · rw [← measure_doubleCoset μ H hH g hHfin]
    exact measure_mono (doubleCoset_mono hHK g)
  · rw [measure_doubleCoset μ K hK g hKfin]
    gcongr
    exact_mod_cast hle

/-- Waldspurger I.1 (5) for abstract data: if `c₁ e(m) ≤ [H : H ∩ m H m⁻¹] ≤ c₂ e(m)` for `m`
in a set `T` (for Waldspurger, `e = δ₀⁻¹` on `T = M̄₀⁺`), then
`c₁ μ(H) e(m) ≤ μ(K m K) ≤ c₂ [K : H] μ(K) e(m)` on `T`. -/
theorem measure_doubleCoset_le_of_doubleCosetIndex {H K : Subgroup G} (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G))
    (hKH : H.relIndex K ≠ 0) {T : Set G} {e : G → ℝ≥0∞} {c₁ c₂ : ℝ≥0∞}
    (hfin : ∀ m ∈ T, doubleCosetIndex H m ≠ 0)
    (hlow : ∀ m ∈ T, c₁ * e m ≤ doubleCosetIndex H m)
    (hup : ∀ m ∈ T, (doubleCosetIndex H m : ℝ≥0∞) ≤ c₂ * e m) {m : G} (hm : m ∈ T) :
    c₁ * μ H * e m ≤ μ (DoubleCoset.doubleCoset m K K) ∧
      μ (DoubleCoset.doubleCoset m K K) ≤ c₂ * H.relIndex K * μ K * e m := by
  obtain ⟨h₁, h₂⟩ := measure_doubleCoset_bounds μ hHK hH hK m (hfin m hm) hKH
  refine ⟨?_, ?_⟩
  · calc c₁ * μ H * e m = c₁ * e m * μ H := by ring
      _ ≤ (doubleCosetIndex H m : ℝ≥0∞) * μ H := by gcongr; exact hlow m hm
      _ ≤ _ := h₁
  · calc μ (DoubleCoset.doubleCoset m K K)
        ≤ (doubleCosetIndex H m : ℝ≥0∞) * H.relIndex K * μ K := h₂
      _ ≤ c₂ * e m * H.relIndex K * μ K := by gcongr; exact hup m hm
      _ = c₂ * H.relIndex K * μ K * e m := by ring

end Measure

section Modulus

variable {U : Type u} [Group U] [MeasurableSpace U] [MeasurableMul U] (ν : Measure U)
  [ν.IsMulLeftInvariant]

/-- The modulus identity for indices: let `φ` be an automorphism of `U` with
`ν(φ(S)) = c ν(S)` for measurable `S`, `Y` a measurable subgroup with `0 < ν(Y) < ∞`, and `Z` a
measurable subgroup of both `Y` and `φ(Y)` of finite index in each. Then
`[Y : Z] c = [φ(Y) : Z]`. For `φ = (u ↦ m u m⁻¹)`, `c = δ(m)` and `Z = Y ∩ m Y m⁻¹` it reads
`[Y : Y ∩ m Y m⁻¹] δ(m) = [m Y m⁻¹ : Y ∩ m Y m⁻¹]`; this is the identity
`c_{U₀}(m) = δ₀(m)⁻¹ c'_{U₀}(m)` in Waldspurger's proof of I.1 (5), whose `c'_{U₀}(m)` is the
right side conjugated by `m⁻¹`. -/
theorem relIndex_mul_modulus (φ : U ≃* U) {c : ℝ≥0∞}
    (hφ : ∀ S : Set U, MeasurableSet S → ν (φ '' S) = c * ν S) {Y Z : Subgroup U}
    (hZY : Z ≤ Y) (hZφY : Z ≤ Y.map φ.toMonoidHom) (hY : MeasurableSet (Y : Set U))
    (hZ : MeasurableSet (Z : Set U)) (hY0 : ν Y ≠ 0) (hYtop : ν Y ≠ ⊤)
    (h₁ : Z.relIndex Y ≠ 0) (h₂ : Z.relIndex (Y.map φ.toMonoidHom) ≠ 0) :
    (Z.relIndex Y : ℝ≥0∞) * c = Z.relIndex (Y.map φ.toMonoidHom) := by
  have hY' := measure_eq_relIndex_mul ν hZY hZ h₁
  have hφY := measure_eq_relIndex_mul ν hZφY hZ h₂
  have hmap : ((Y.map φ.toMonoidHom : Subgroup U) : Set U) = φ '' (Y : Set U) := by
    ext x; simp
  rw [hmap, hφ _ hY, hY'] at hφY
  have hZ0 : ν Z ≠ 0 := by
    intro h; rw [h, mul_zero] at hY'; exact hY0 hY'
  have hZtop : ν Z ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by exact_mod_cast h₁)] at hY'
    exact hYtop hY'
  refine (ENNReal.mul_left_inj hZ0 hZtop).mp ?_
  rw [← hφY]
  ring

end Modulus

end Langlands.HarishChandraSchwartz
