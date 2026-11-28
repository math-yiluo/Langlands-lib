import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Packing and fibre bounds for invariant measures on groups

Two elementary measure inequalities on a group `G` with a left-invariant measure `μ`.

* `finite_inter_and_ncard_mul_le` (packing): if `Γ` is a subgroup and the only point of `Γ` in
  `W W⁻¹` is `1`, then the left translates `γ W` (`γ ∈ Γ ∩ Z`) are disjoint subsets of `Z W`, so
  `Γ ∩ Z` is finite and `#(Γ ∩ Z) μ(W) ≤ μ(Z W)` whenever `0 < μ(W)` and `μ(Z W) < ∞`.
* `measure_mul_mul_le` (fibre bound): for a subgroup `H` with a left-invariant measure `ν`,
  subsets `X, V ⊆ H` and `B ⊆ G`, `μ(X B) ν(V) ≤ ν(X V) μ(V⁻¹ B)`, by Tonelli's theorem on `H × G`.
-/

noncomputable section

open MeasureTheory Set
open scoped Pointwise ENNReal

namespace Langlands.HaarPacking

section Packing

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- The left translates by points of `Γ ∩ Z` of a set `W` whose quotient set `W W⁻¹` meets `Γ`
only in `1` are disjoint subsets of `Z W`. -/
theorem card_mul_measure_le (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G)
    {W : Set G} (hW : MeasurableSet W) (hsep : ∀ γ ∈ Γ, γ ∈ W * W⁻¹ → γ = 1)
    (Z : Set G) (s : Finset G) (hs : (s : Set G) ⊆ (Γ : Set G) ∩ Z) :
    (s.card : ℝ≥0∞) * μ W ≤ μ (Z * W) := by
  have hdisj : PairwiseDisjoint (s : Set G) (fun γ => γ • W) := by
    intro γ hγ γ' hγ' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨w, hw, rfl⟩ ⟨w', hw', hx⟩
    apply hne
    have hmem : γ'⁻¹ * γ ∈ Γ := Γ.mul_mem (Γ.inv_mem (hs hγ').1) (hs hγ).1
    have heq : γ'⁻¹ * γ = w' * w⁻¹ := by
      simp only [smul_eq_mul] at hx
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hx, inv_mul_cancel_left]
    have hWW : γ'⁻¹ * γ ∈ W * W⁻¹ :=
      heq ▸ Set.mul_mem_mul hw' (Set.inv_mem_inv.mpr hw)
    have h1 := hsep _ hmem hWW
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hunion : (⋃ γ ∈ s, γ • W) ⊆ Z * W := by
    simp only [Set.iUnion_subset_iff]
    rintro γ hγ _ ⟨w, hw, rfl⟩
    exact Set.mul_mem_mul (hs hγ).2 hw
  calc (s.card : ℝ≥0∞) * μ W = ∑ γ ∈ s, μ (γ • W) := by
        simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
    _ = μ (⋃ γ ∈ s, γ • W) :=
        (measure_biUnion_finset hdisj fun γ _ => hW.const_smul γ).symm
    _ ≤ μ (Z * W) := measure_mono hunion

/-- **Packing.** If `Γ` meets `W W⁻¹` only in `1`, `μ(W) > 0` and `μ(Z W) < ∞`, then `Γ ∩ Z` is
finite and `#(Γ ∩ Z) μ(W) ≤ μ(Z W)`. -/
theorem finite_inter_and_ncard_mul_le (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G)
    {W : Set G} (hW : MeasurableSet W) (hW0 : μ W ≠ 0) (hsep : ∀ γ ∈ Γ, γ ∈ W * W⁻¹ → γ = 1)
    (Z : Set G) (hZ : μ (Z * W) ≠ ∞) :
    ((Γ : Set G) ∩ Z).Finite ∧ ((((Γ : Set G) ∩ Z).ncard : ℕ) : ℝ≥0∞) * μ W ≤ μ (Z * W) := by
  have hfin : ((Γ : Set G) ∩ Z).Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hW0 hZ
    obtain ⟨t, ht, htcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have h := card_mul_measure_le μ Γ hW hsep Z t ht
    rw [htcard] at h
    exact absurd (h.trans_lt hn) (lt_irrefl _)
  refine ⟨hfin, ?_⟩
  have h := card_mul_measure_le μ Γ hW hsep Z hfin.toFinset (by simp)
  rwa [Set.ncard_eq_toFinset_card _ hfin]

end Packing

section Fibre

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **Fibre bound.** Let `H` be a subgroup of `G`, `μ` a left-invariant measure on `G` and `ν` a
left-invariant measure on `H`. For `X, V ⊆ H` and `B ⊆ G` with `X V` and `V⁻¹ B` measurable,
`μ(X B) ν(V) ≤ ν(X V) μ(V⁻¹ B)`. Every point `x b` of `X B` has at least the `ν`-mass `ν(x V)`
of points `h ∈ X V` with `h⁻¹ x b ∈ V⁻¹ B`; integrate over `H × G`. -/
theorem measure_mul_mul_le (H : Subgroup G) [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (ν : Measure H) [ν.IsMulLeftInvariant] [SFinite ν]
    {X V : Set H} {B : Set G} (hXV : MeasurableSet (X * V))
    (hD : MeasurableSet (((Subtype.val '' V : Set G))⁻¹ * B)) :
    μ ((Subtype.val '' X : Set G) * B) * ν V ≤
      ν (X * V) * μ ((Subtype.val '' V : Set G)⁻¹ * B) := by
  set D : Set G := (Subtype.val '' V : Set G)⁻¹ * B with hDdef
  set S : Set (H × G) := {p | p.1 ∈ X * V ∧ (p.1 : G)⁻¹ * p.2 ∈ D} with hSdef
  have hval : Measurable (Subtype.val : H → G) := continuous_subtype_val.measurable
  have hf : Measurable fun p : H × G => (p.1 : G)⁻¹ * p.2 :=
    (hval.comp measurable_fst).inv.mul measurable_snd
  have hS : MeasurableSet S := (measurable_fst hXV).inter (hf hD)
  have h1 : (ν.prod μ) S = ν (X * V) * μ D := by
    rw [Measure.prod_apply hS]
    have hslice : ∀ h : H, μ (Prod.mk h ⁻¹' S) = (X * V).indicator (fun _ => μ D) h := by
      intro h
      by_cases hh : h ∈ X * V
      · rw [indicator_of_mem hh]
        have : Prod.mk h ⁻¹' S = (h : G) • D := by
          ext g
          simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, hh, true_and,
            Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
        rw [this, measure_smul]
      · rw [indicator_of_notMem hh]
        have : Prod.mk h ⁻¹' S = ∅ := by
          ext g
          simp [hSdef, hh]
        rw [this, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator hXV, setLIntegral_const, mul_comm]
  have h2 : (ν.prod μ) S = ∫⁻ g, ν ((fun h => (h, g)) ⁻¹' S) ∂μ := Measure.prod_apply_symm hS
  have hmeas : Measurable fun g => ν ((fun h => (h, g)) ⁻¹' S) :=
    measurable_measure_prodMk_right hS
  have hsub : (Subtype.val '' X : Set G) * B ⊆ {g | ν V ≤ ν ((fun h => (h, g)) ⁻¹' S)} := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    have hxV : x • V ⊆ (fun h => (h, (x : G) * b)) ⁻¹' S := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨Set.mul_mem_mul hx hv, ?_⟩
      have : ((x • v : H) : G)⁻¹ * ((x : G) * b) = (v : G)⁻¹ * b := by
        simp only [smul_eq_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact Set.mul_mem_mul (Set.inv_mem_inv.mpr ⟨v, hv, rfl⟩) hb
    calc ν V = ν (x • V) := (measure_smul ν x V).symm
      _ ≤ _ := measure_mono hxV
  calc μ ((Subtype.val '' X : Set G) * B) * ν V
      ≤ μ {g | ν V ≤ ν ((fun h => (h, g)) ⁻¹' S)} * ν V := by gcongr
    _ = ν V * μ {g | ν V ≤ ν ((fun h => (h, g)) ⁻¹' S)} := mul_comm _ _
    _ ≤ ∫⁻ g, ν ((fun h => (h, g)) ⁻¹' S) ∂μ := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable _
    _ = (ν.prod μ) S := h2.symm
    _ = ν (X * V) * μ D := h1

end Fibre

end Langlands.HaarPacking
