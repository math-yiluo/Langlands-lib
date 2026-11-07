import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Continuity of roots over a henselian field algebraically closed in its completion

Let `K` be a henselian valued field that is algebraically closed in its completion. If monic
polynomials `p i` of a fixed degree converge coefficientwise to a monic polynomial `p₀` along
an ultrafilter, then roots `t i ∈ K` of `p i` converge along the ultrafilter to a root of `p₀`
in `K`. This is the "continuity of roots" input of Conrad's proof of Corollary 5.12, which
cites [BGR, 3.4.1/2] over complete fields.

The roots stay bounded and `p₀(t i) → 0`. Over an algebraic closure with the unique extension
of the absolute value, `p₀` is a product of linear factors, so along the ultrafilter `t i`
approaches one root `ρ`, hence is Cauchy. Its limit in the completion is a root of `p₀`,
hence algebraic over `K`, hence lies in `K`.
-/

noncomputable section

universe u

open Polynomial Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianRootContinuity

variable {K : Type u} [NontriviallyNormedField K]

/-- **Cauchy's bound.** A root of a monic polynomial has norm at most
`max 1 (∑_{n < deg} ‖coeff n‖)`. -/
theorem norm_le_of_isRoot {p : K[X]} (hp : p.Monic) {t : K} (ht : p.IsRoot t) :
    ‖t‖ ≤ max 1 (∑ n ∈ Finset.range p.natDegree, ‖p.coeff n‖) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := max_lt_iff.mp h
  set d := p.natDegree with hd
  have hd0 : d ≠ 0 := by
    intro h0
    rw [eq_one_of_monic_natDegree_zero hp h0, IsRoot.def, eval_one] at ht
    exact one_ne_zero ht
  have hsum : t ^ d = -∑ n ∈ Finset.range d, p.coeff n * t ^ n := by
    have h := ht
    rw [IsRoot.def, eval_eq_sum_range, Finset.sum_range_succ, ← hd, hp.coeff_natDegree,
      one_mul] at h
    linear_combination h
  have ht0 : 0 < ‖t‖ := lt_trans one_pos h1
  have hle : ‖t‖ ^ d ≤ (∑ n ∈ Finset.range d, ‖p.coeff n‖) * ‖t‖ ^ (d - 1) := by
    calc ‖t‖ ^ d = ‖t ^ d‖ := (norm_pow t d).symm
      _ = ‖∑ n ∈ Finset.range d, p.coeff n * t ^ n‖ := by rw [hsum, norm_neg]
      _ ≤ ∑ n ∈ Finset.range d, ‖p.coeff n * t ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range d, ‖p.coeff n‖ * ‖t‖ ^ (d - 1) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_mul, norm_pow]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact pow_le_pow_right₀ h1.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hn))
      _ = (∑ n ∈ Finset.range d, ‖p.coeff n‖) * ‖t‖ ^ (d - 1) := (Finset.sum_mul _ _ _).symm
  have hpow : ‖t‖ ^ d = ‖t‖ * ‖t‖ ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hle
  have := le_of_mul_le_mul_right hle (pow_pos ht0 _)
  linarith

/-- An absolute value of a product of linear factors is the product of the absolute values. -/
theorem abv_prod_sub {L : Type u} [Field L] (v : AbsoluteValue L ℝ) (a : L) (s : Multiset L) :
    v (s.map (a - ·)).prod = (s.map fun ρ => v (a - ρ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ρ s ih => simp [ih]

/-- If every factor is at least `c ≥ 0`, the product is at least `c ^ card`. -/
theorem pow_card_le_prod {L : Type u} [Field L] (v : AbsoluteValue L ℝ) (a : L) {c : ℝ}
    (hc : 0 ≤ c) (s : Multiset L) (h : ∀ ρ ∈ s, c ≤ v (a - ρ)) :
    c ^ Multiset.card s ≤ (s.map fun ρ => v (a - ρ)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ρ s ih =>
    rw [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons]
    refine mul_le_mul (h ρ (Multiset.mem_cons_self _ _))
      (ih fun ρ' hρ' => h ρ' (Multiset.mem_cons_of_mem hρ')) (pow_nonneg hc _)
      (v.nonneg _)

local notation "K̂" => UniformSpace.Completion K

/-- **Continuity of roots.** Let `K` be henselian and algebraically closed in its completion.
If monic polynomials `p i` of the same degree as a monic `p₀` converge to `p₀`
coefficientwise along an ultrafilter `l`, and `t i ∈ K` is a root of `p i`, then `t i`
converges along `l` to a root of `p₀` in `K`. -/
theorem exists_tendsto_root (hK : IsHenselianValuedField K)
    (hcl : algebraicClosure K K̂ = ⊥) {ι : Type*} (l : Ultrafilter ι) (p : ι → K[X])
    (p₀ : K[X]) (hp₀ : p₀.Monic) (hp : ∀ i, (p i).Monic)
    (hdeg : ∀ i, (p i).natDegree = p₀.natDegree)
    (hcoeff : ∀ n, Tendsto (fun i => (p i).coeff n) l (𝓝 (p₀.coeff n)))
    (t : ι → K) (ht : ∀ i, (p i).IsRoot (t i)) :
    ∃ τ : K, p₀.IsRoot τ ∧ Tendsto t l (𝓝 τ) := by
  classical
  set d := p₀.natDegree with hd
  -- the roots stay bounded
  let M : ℝ := ∑ n ∈ Finset.range d, ‖p₀.coeff n‖
  let B : ℝ := max 1 (M + 1)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hbound : ∀ᶠ i in (l : Filter ι), ‖t i‖ ≤ B := by
    have hsum : Tendsto (fun i => ∑ n ∈ Finset.range d, ‖(p i).coeff n‖) l (𝓝 M) :=
      tendsto_finsetSum _ fun n _ => (hcoeff n).norm
    filter_upwards [hsum.eventually (gt_mem_nhds (lt_add_one M))] with i hi
    have h := norm_le_of_isRoot (hp i) (ht i)
    rw [hdeg i] at h
    exact h.trans (max_le_max le_rfl hi.le)
  -- `p₀` is small at the roots
  have hsmall : Tendsto (fun i => p₀.eval (t i)) l (𝓝 0) := by
    have hdiff : Tendsto (fun i => ∑ n ∈ Finset.range (d + 1),
        ‖p₀.coeff n - (p i).coeff n‖ * B ^ n) l (𝓝 0) := by
      have : (0 : ℝ) = ∑ n ∈ Finset.range (d + 1), ‖p₀.coeff n - p₀.coeff n‖ * B ^ n := by
        simp
      rw [this]
      refine tendsto_finsetSum _ fun n _ => ?_
      exact (((tendsto_const_nhds (x := p₀.coeff n)).sub (hcoeff n)).norm).mul_const _
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hdiff
    filter_upwards [hbound] with i hi
    have e : p₀.eval (t i) = ∑ n ∈ Finset.range (d + 1),
        (p₀.coeff n - (p i).coeff n) * t i ^ n := by
      have h₁ := eval_eq_sum_range' (p := p₀) (n := d + 1) (by omega) (t i)
      have h₂ := eval_eq_sum_range' (p := p i) (n := d + 1) (by rw [hdeg i]; omega) (t i)
      have h₃ : (p i).eval (t i) = 0 := ht i
      rw [h₁, ← sub_zero (∑ n ∈ _, _), ← h₃, h₂, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hi n) (norm_nonneg _)
  -- factor `p₀` over an algebraic closure with the henselian absolute value
  let L := AlgebraicClosure K
  obtain ⟨v, hv⟩ := (hK L).exists
  let q := p₀.map (algebraMap K L)
  have hqs : Splits q := IsAlgClosed.splits q
  have hqm : q.Monic := hp₀.map _
  have hqd : Multiset.card q.roots = d := by
    rw [← hqs.natDegree_eq_card_roots, natDegree_map]
  obtain ⟨i₀, -⟩ := l.neBot.nonempty_of_mem Filter.univ_mem
  have hd0 : d ≠ 0 := by
    intro h0
    have h := ht i₀
    rw [eq_one_of_monic_natDegree_zero (hp i₀) ((hdeg i₀).trans h0), IsRoot.def,
      eval_one] at h
    exact one_ne_zero h
  have hroots : q.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hqd
    exact hd0 hqd.symm
  have hnorm : ∀ x : K, ‖p₀.eval x‖ =
      (q.roots.map fun ρ => v (algebraMap K L x - ρ)).prod := by
    intro x
    rw [← hv, ← abv_prod_sub, ← hqs.eval_eq_prod_roots_of_monic hqm, eval_map,
      eval₂_at_apply]
  -- along the ultrafilter the roots approach one root `ρ` of `p₀`
  have hcover : ∀ i, ∃ ρ ∈ q.roots.toFinset,
      v (algebraMap K L (t i) - ρ) ^ d ≤ ‖p₀.eval (t i)‖ := by
    intro i
    obtain ⟨ρ, hρ, hmin⟩ := Multiset.exists_min_image (fun ρ => v (algebraMap K L (t i) - ρ))
      hroots
    refine ⟨ρ, Multiset.mem_toFinset.mpr hρ, ?_⟩
    rw [hnorm, ← hqd]
    exact pow_card_le_prod v _ (v.nonneg _) _ fun ρ' hρ' => hmin ρ' hρ'
  have huniv : (⋃ ρ ∈ (q.roots.toFinset : Set L),
      {i | v (algebraMap K L (t i) - ρ) ^ d ≤ ‖p₀.eval (t i)‖}) ∈ l := by
    refine Filter.mem_of_superset Filter.univ_mem fun i _ => ?_
    obtain ⟨ρ, hρ, h⟩ := hcover i
    exact Set.mem_biUnion (Finset.mem_coe.mpr hρ) h
  obtain ⟨ρ, -, hρl⟩ := (Ultrafilter.finite_biUnion_mem_iff q.roots.toFinset.finite_toSet).mp huniv
  have hclose : ∀ ε > 0, {i | v (algebraMap K L (t i) - ρ) < ε} ∈ l := by
    intro ε hε
    filter_upwards [hρl, (tendsto_zero_iff_norm_tendsto_zero.mp hsmall).eventually
      (gt_mem_nhds (pow_pos hε d))] with i hi hi'
    exact (pow_lt_pow_iff_left₀ (v.nonneg _) hε.le hd0).mp (lt_of_le_of_lt hi hi')
  -- hence the roots form a Cauchy family
  have hcauchy : Cauchy (Filter.map t l) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨t '' {i | v (algebraMap K L (t i) - ρ) < ε / 2},
      Filter.mem_map.mpr (Filter.mem_of_superset (hclose _ (half_pos hε))
        (Set.subset_preimage_image _ _)), ?_⟩⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    rw [dist_eq_norm, ← hv, map_sub]
    calc v (algebraMap K L (t i) - algebraMap K L (t j)) ≤
          v (algebraMap K L (t i) - ρ) + v (ρ - algebraMap K L (t j)) := v.sub_le _ _ _
      _ < ε / 2 + ε / 2 := by
          rw [← v.map_neg (ρ - _), neg_sub]
          exact add_lt_add hi hj
      _ = ε := add_halves ε
  -- its limit in the completion is a root of `p₀`, hence lies in `K`
  obtain ⟨τc, hτc⟩ := CompleteSpace.complete
    (hcauchy.map (UniformSpace.Completion.uniformContinuous_coe K))
  have hτc' : Tendsto (fun i => (t i : K̂)) l (𝓝 τc) := by
    rw [Filter.map_map] at hτc
    exact hτc
  have hroot : (p₀.map (algebraMap K K̂)).eval τc = 0 := by
    have h₁ : Tendsto (fun i => (p₀.map (algebraMap K K̂)).eval (t i : K̂)) l
        (𝓝 ((p₀.map (algebraMap K K̂)).eval τc)) :=
      ((p₀.map (algebraMap K K̂)).continuous.tendsto τc).comp hτc'
    have h₂ : Tendsto (fun i => (p₀.map (algebraMap K K̂)).eval (t i : K̂)) l (𝓝 0) := by
      have e : (fun i => (p₀.map (algebraMap K K̂)).eval (t i : K̂)) =
          fun i => ((p₀.eval (t i) : K) : K̂) := by
        funext i
        rw [eval_map]
        exact eval₂_at_apply (algebraMap K K̂) (t i)
      rw [e, ← UniformSpace.Completion.coe_zero]
      exact (UniformSpace.Completion.continuous_coe K).continuousAt.tendsto.comp hsmall
    exact tendsto_nhds_unique h₁ h₂
  have halg : IsAlgebraic K τc :=
    ⟨p₀, hp₀.ne_zero, by rw [aeval_def, ← eval_map]; exact hroot⟩
  have hmem : τc ∈ algebraicClosure K K̂ := mem_algebraicClosure_iff.mpr halg
  rw [hcl] at hmem
  obtain ⟨τ, hτ⟩ := IntermediateField.mem_bot.mp hmem
  have hemb := (UniformSpace.Completion.isUniformEmbedding_coe K).isEmbedding
  refine ⟨τ, ?_, ?_⟩
  · apply hemb.injective
    rw [UniformSpace.Completion.coe_zero, ← hroot, ← hτ, eval_map]
    exact (eval₂_at_apply (algebraMap K K̂) τ).symm
  · rw [hemb.isInducing.tendsto_nhds_iff]
    change Tendsto (fun i => (t i : K̂)) l (𝓝 (algebraMap K K̂ τ))
    rw [hτ]
    exact hτc'

end HenselianRootContinuity

end Langlands.AlgebraicGeometry.PointTopology
