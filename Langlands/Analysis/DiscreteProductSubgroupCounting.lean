import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-! # Polynomial counting for a discrete additive subgroup with a compact second slice -/

noncomputable section

universe u v

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal Function

namespace Langlands.Analysis

section Packing

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Haar packing argument applies to a finite family of separated centres, with
arbitrary ball and separation radii. -/
private theorem card_le_of_separated_centres {ι : Type v} (s : Finset ι) (f : ι → E)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hs : ∀ i ∈ s, ‖f i‖ ≤ R)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ε + ε ≤ dist (f i) (f j)) :
    (s.card : ℝ) ≤ ((R + ε) / ε) ^ Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hpos : 0 < R + ε := add_pos_of_nonneg_of_pos hR hε
  have hD : PairwiseDisjoint (↑s : Set ι) (fun i => ball (f i) ε) :=
    fun i hi j hj hij => ball_disjoint_ball (hsep i hi j hj hij)
  have hsub : (⋃ i ∈ s, ball (f i) ε) ⊆ ball (0 : E) (R + ε) := by
    refine iUnion₂_subset fun i hi => ball_subset_ball' ?_
    rw [dist_zero_right, add_comm R ε]
    exact add_le_add_right (hs i hi) ε
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (ε ^ Module.finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + ε) ^ Module.finrank ℝ E) * μ (ball 0 1) := calc
    _ = μ (⋃ i ∈ s, ball (f i) ε) := by
      rw [measure_biUnion_finset hD (fun _ _ => measurableSet_ball)]
      simp only [μ.addHaar_ball_of_pos _ hε, Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ μ (ball (0 : E) (R + ε)) := measure_mono hsub
    _ = _ := μ.addHaar_ball_of_pos _ hpos
  have hcancel := (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp hvol
  have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hpos.le _) hcancel
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hε _)).mpr
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hε.le _)] using h

end Packing

/-- Numbers of lattice points in growing balls with a fixed compact second slice are
finite and at most polynomial, with degree the real dimension of the ball factor. -/
def DiscreteProductSubgroupCountingStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Type v} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
    (Γ : AddSubgroup (E × A)) [DiscreteTopology Γ] (C : Set A), IsCompact C →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
        let P := (Γ : Set (E × A)) ∩ (closedBall (0 : E) R ×ˢ C)
        P.Finite ∧ (P.ncard : ℝ) ≤ B * (1 + R) ^ Module.finrank ℝ E

/-- A finite compact cover in the second coordinate gives a fixed separation
scale in the first coordinate. -/
theorem discreteProductSubgroupCounting : DiscreteProductSubgroupCountingStatement.{u, v} := by
  classical
  intro E _ _ _ A _ _ _ _ Γ _ C hC
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Γ))
  have hzero : (0 : E × A) ∈ U := by
    change (0 : Γ) ∈ Subtype.val ⁻¹' U
    rw [hUeq]
    exact mem_singleton _
  have hiso (p : E × A) (hp : p ∈ Γ) (hpu : p ∈ U) : p = 0 := by
    have h : (⟨p, hp⟩ : Γ) ∈ Subtype.val ⁻¹' U := hpu
    rw [hUeq] at h
    exact congrArg Subtype.val (mem_singleton_iff.mp h)
  obtain ⟨V, hV, W, hW, hprod⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hzero)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hsubW : (fun p : A × A => p.1 - p.2) ⁻¹' W ∈ 𝓝 (0, 0) :=
    (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨W₁, hW₁, W₂, hW₂, hWW⟩ := mem_nhds_prod_iff.mp hsubW
  let O : Set A := interior (W₁ ∩ W₂)
  have hO0 : (0 : A) ∈ O := mem_interior_iff_mem_nhds.mpr (inter_mem hW₁ hW₂)
  let cover (a : A) := (fun b => b - a) ⁻¹' O
  have hcover : C ⊆ ⋃ a, cover a := by
    intro a _
    exact mem_iUnion.mpr ⟨a, by simpa [cover] using hO0⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover cover
    (fun a => isOpen_interior.preimage (continuous_id.sub (continuous_const (y := a)))) hcover
  let ε : ℝ := r / 2
  have hε : 0 < ε := half_pos hr
  let d := Module.finrank ℝ E
  let L : ℝ := max 1 ε / ε
  have hL : 0 ≤ L := div_nonneg (le_trans zero_le_one (le_max_left _ _)) hε.le
  refine ⟨(t.card : ℝ) * L ^ d, by positivity, ?_⟩
  intro R hR
  let P := (Γ : Set (E × A)) ∩ (closedBall (0 : E) R ×ˢ C)
  change P.Finite ∧ (P.ncard : ℝ) ≤ _
  have hP : P.Finite := by
    have hcP : IsCompact P := ((isCompact_closedBall (0 : E) R).prod hC).inter_left
      AddSubgroup.isClosed_of_discreteTopology
    exact hcP.finite ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ)).mono
      inter_subset_left)
  let piece (a : A) := P ∩ Prod.snd ⁻¹' cover a
  have hfinite (a : A) : (piece a).Finite := hP.subset inter_subset_left
  have hsep (a : A) : ∀ p ∈ piece a, ∀ q ∈ piece a, p ≠ q →
      ε + ε ≤ dist p.1 q.1 := by
    intro p hp q hq hpq
    by_contra! hd
    have hE : (p - q).1 ∈ V := hrV (by
      apply mem_ball_zero_iff.mpr
      change ‖p.1 - q.1‖ < r
      rwa [← dist_eq_norm, show r = ε + ε by dsimp [ε]; ring])
    have hA : (p - q).2 ∈ W := by
      change p.2 - q.2 ∈ W
      have hpO : p.2 - a ∈ O := hp.2
      have hqO : q.2 - a ∈ O := hq.2
      have hh := hWW (show (p.2 - a, q.2 - a) ∈ W₁ ×ˢ W₂ from
        ⟨(interior_subset hpO).1, (interior_subset hqO).2⟩)
      change (p.2 - a) - (q.2 - a) ∈ W at hh
      simpa only [sub_sub_sub_cancel_right] using hh
    exact hpq (sub_eq_zero.mp (hiso (p - q) (Γ.sub_mem hp.1.1 hq.1.1) (hprod ⟨hE, hA⟩)))
  have hpiece (a : A) : ((piece a).ncard : ℝ) ≤ L ^ d * (1 + R) ^ d := by
    rw [Set.ncard_eq_toFinset_card _ (hfinite a)]
    have hN := card_le_of_separated_centres (hfinite a).toFinset Prod.fst hR hε
      (fun p hp => mem_closedBall_zero_iff.mp (((hfinite a).mem_toFinset.mp hp).1.2.1))
      (fun p hp q hq hpq => hsep a p ((hfinite a).mem_toFinset.mp hp) q
        ((hfinite a).mem_toFinset.mp hq) hpq)
    refine hN.trans ?_
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hle : R + ε ≤ max 1 ε * (1 + R) := by
      calc
        R + ε ≤ max 1 ε * R + max 1 ε :=
          add_le_add (le_mul_of_one_le_left hR (le_max_left _ _)) (le_max_right _ _)
        _ = _ := by ring
    calc
      (R + ε) / ε ≤ (max 1 ε * (1 + R)) / ε := div_le_div_of_nonneg_right hle hε.le
      _ = L * (1 + R) := by dsimp [L]; ring
  have heq : P = ⋃ a ∈ t, piece a := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨a, ha⟩ := mem_iUnion.mp (ht hp.2.2)
      obtain ⟨hat, hpa⟩ := mem_iUnion.mp ha
      exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨hat, hp, hpa⟩⟩
    · exact iUnion₂_subset fun _ _ => inter_subset_left
  refine ⟨hP, ?_⟩
  calc
    (P.ncard : ℝ) ≤ ∑ a ∈ t, ((piece a).ncard : ℝ) := by
      rw [heq, ← Nat.cast_sum]
      exact_mod_cast t.set_ncard_biUnion_le piece
    _ ≤ ∑ _a ∈ t, L ^ d * (1 + R) ^ d := Finset.sum_le_sum fun a _ => hpiece a
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc, d]

end Langlands.Analysis
