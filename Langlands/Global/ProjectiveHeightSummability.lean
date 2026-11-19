import Langlands.Global.NumberFieldHeightCountProof
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Summability of inverse heights of rational projective points -/

noncomputable section

namespace Langlands.Global

open Height

private theorem summable_rpow_of_polynomial_height_count {α : Type*} (H : α → ℝ)
    (hH : ∀ x, 1 ≤ H x) {C : ℝ} {M : ℕ}
    (hfinite : ∀ B : ℝ, 1 ≤ B → {x | H x ≤ B}.Finite)
    (hcount : ∀ B : ℝ, 1 ≤ B → ({x | H x ≤ B}.ncard : ℝ) ≤ C * B ^ M)
    {s : ℝ} (hs : (M : ℝ) + 2 ≤ s) :
    Summable (fun x => H x ^ (-s)) := by
  classical
  have hC : 0 ≤ C := by
    simpa using (Nat.cast_nonneg _).trans (hcount 1 le_rfl)
  let shell (x : α) : ℕ := ⌊H x⌋₊ - 1
  let fiber (n : ℕ) : Set α := {x | shell x = n}
  have bounds (n : ℕ) (x : fiber n) : (n : ℝ) + 1 ≤ H x ∧ H x ≤ (n : ℝ) + 2 := by
    have hone : 1 ≤ ⌊H (x : α)⌋₊ := Nat.le_floor (by simpa using hH x)
    have hn : ⌊H (x : α)⌋₊ - 1 = n := x.property
    have hfloor : ⌊H (x : α)⌋₊ = n + 1 := by omega
    refine ⟨?_, ?_⟩
    · simpa [hfloor] using Nat.floor_le (zero_le_one.trans (hH x))
    · have h := (Nat.lt_floor_add_one (H x)).le
      rw [hfloor, Nat.cast_add, Nat.cast_one] at h
      linarith
  have subset_sublevel (n : ℕ) : fiber n ⊆ {x | H x ≤ (n : ℝ) + 2} :=
    fun x hx => (bounds n ⟨x, hx⟩).2
  have hone (n : ℕ) : 1 ≤ (n : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  let fiberFintype (n : ℕ) : Fintype (fiber n) :=
    ((hfinite _ (hone n)).subset (subset_sublevel n)).fintype
  let weight (x : α) : ℝ := H x ^ (-s)
  have hw (x : α) : 0 ≤ weight x := Real.rpow_nonneg (zero_le_one.trans (hH x)) _
  suffices h : Summable (fun x : Σ n, fiber n => weight x.2.val) by
    exact (Equiv.sigmaFiberEquiv shell).summable_iff.mp h
  have hnonneg (x : Σ n, fiber n) : 0 ≤ weight x.2.val := hw _
  refine (summable_sigma_of_nonneg hnonneg).2 ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hseries : Summable (fun n : ℕ => (C * 2 ^ M) * ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (hp.comp_injective Nat.succ_injective).mul_left (C * 2 ^ M)
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun x : fiber n => hw x)) ?_ hseries
  intro n
  let t : ℝ := (n : ℝ) + 1
  have ht : 1 ≤ t := by simp [t]
  have ht_pos : 0 < t := zero_lt_one.trans_le ht
  have hdouble : (n : ℝ) + 2 ≤ 2 * t := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcard : (Fintype.card (fiber n) : ℝ) ≤ C * (2 * t) ^ M := by
    rw [Set.fintypeCard_eq_ncard]
    calc
      _ ≤ ({x | H x ≤ (n : ℝ) + 2}.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard (subset_sublevel n) (hfinite _ (hone n))
      _ ≤ C * ((n : ℝ) + 2) ^ M := hcount _ (hone n)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdouble _) hC
  have hterm (x : fiber n) : H x ^ (-s) ≤ t ^ (-(M : ℝ) - 2) :=
    (Real.rpow_le_rpow_of_nonpos ht_pos (bounds n x).1 (by linarith [Nat.cast_nonneg (α := ℝ) M])).trans
      (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
  change (∑' x : fiber n, H x ^ (-s)) ≤ (C * 2 ^ M) * t ^ (-2 : ℝ)
  calc
    _ = ∑ x : fiber n, H x ^ (-s) := tsum_fintype _
    _ ≤ ∑ _ : fiber n, t ^ (-(M : ℝ) - 2) := Finset.sum_le_sum fun x _ => hterm x
    _ = (Fintype.card (fiber n) : ℝ) * t ^ (-(M : ℝ) - 2) := by simp
    _ ≤ (C * (2 * t) ^ M) * t ^ (-(M : ℝ) - 2) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg ht_pos.le _)
    _ = (C * 2 ^ M) * t ^ (-2 : ℝ) := by
      rw [mul_pow, ← mul_assoc C, mul_assoc (C * 2 ^ M), ← Real.rpow_natCast t M,
        ← Real.rpow_add ht_pos, show (M : ℝ) + (-(M : ℝ) - 2) = -2 by ring]

section Coordinates

variable {K : Type*} [Field K] {ι : Type*}

private def projectivePivot (p : Projectivization K (ι → K)) : ι :=
  Classical.choose (Function.ne_iff.mp p.rep_nonzero)

private theorem projectivePivot_ne_zero (p : Projectivization K (ι → K)) :
    p.rep (projectivePivot p) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp p.rep_nonzero)

private def normalizedCoordinates (p : Projectivization K (ι → K)) : ι → K :=
  fun j => p.rep j / p.rep (projectivePivot p)

private theorem normalizedCoordinates_injective :
    Function.Injective (normalizedCoordinates (K := K) (ι := ι)) := by
  intro p q hpq
  have hscaled :
      (p.rep (projectivePivot p))⁻¹ • p.rep = (q.rep (projectivePivot q))⁻¹ • q.rep := by
    funext j
    simpa only [normalizedCoordinates, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul] using
      congrFun hpq j
  calc
    p = Projectivization.mk K p.rep p.rep_nonzero := p.mk_rep.symm
    _ = Projectivization.mk K q.rep q.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨p.rep (projectivePivot p) * (q.rep (projectivePivot q))⁻¹, ?_⟩
      rw [← smul_smul, ← hscaled, smul_smul, mul_inv_cancel₀ (projectivePivot_ne_zero p), one_smul]
    _ = q := q.mk_rep

private theorem mulHeight₁_normalizedCoordinates_le [AdmissibleAbsValues K] [Finite ι]
    (p : Projectivization K (ι → K)) (j : ι) :
    mulHeight₁ (normalizedCoordinates p j) ≤ p.mulHeight := by
  have hpair : p.rep ∘ (![j, projectivePivot p] : Fin 2 → ι) =
      ![p.rep j, p.rep (projectivePivot p)] := by
    funext k
    fin_cases k <;> rfl
  have h := Height.mulHeight_comp_le (![j, projectivePivot p] : Fin 2 → ι) p.rep
  rw [hpair, ← Projectivization.mulHeight_mk p.rep_nonzero, p.mk_rep] at h
  simpa only [normalizedCoordinates, Height.mulHeight₁_div_eq_mulHeight] using h

end Coordinates

section ProjectiveTuple

variable {K : Type*} [Field K] [AdmissibleAbsValues K]
  {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]

/-- The product of the multiplicative Weil heights of a finite tuple of projective points. -/
def projectiveTupleHeight (p : ∀ i, Projectivization K (J i → K)) : ℝ :=
  ∏ i, (p i).mulHeight

theorem one_le_projectiveTupleHeight (p : ∀ i, Projectivization K (J i → K)) :
    1 ≤ projectiveTupleHeight p :=
  Finset.one_le_prod₀ fun i _ => (p i).one_le_mulHeight

theorem mulHeight_le_projectiveTupleHeight (p : ∀ i, Projectivization K (J i → K))
    (i : I) : (p i).mulHeight ≤ projectiveTupleHeight p := by
  simpa only [projectiveTupleHeight, max_eq_left (Projectivization.one_le_mulHeight _)] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => (p j).mulHeight)

end ProjectiveTuple

private theorem projectiveTupleHeight_count (K : Type*) [Field K] [NumberField K]
    {I : Type*} [Fintype I] (J : I → Type*) [∀ i, Fintype (J i)] :
    ∃ C : ℝ, ∃ M : ℕ, ∀ B : ℝ, 1 ≤ B →
      let S := {p : ∀ i, Projectivization K (J i → K) | projectiveTupleHeight p ≤ B}
      S.Finite ∧ (S.ncard : ℝ) ≤ C * B ^ M := by
  classical
  obtain ⟨C, M, hcount⟩ := numberFieldMulHeightCount K
  let d := Fintype.card (Σ i, J i)
  refine ⟨C ^ d, M * d, ?_⟩
  intro B hB S
  let T : Set K := {x | mulHeight₁ x ≤ B}
  let : Fintype T := (NumberField.finite_setOfPred_mulHeight₁_le K B).fintype
  let encode (p : S) (j : Σ i, J i) : T :=
    ⟨normalizedCoordinates (p.val j.1) j.2,
      (mulHeight₁_normalizedCoordinates_le (p.val j.1) j.2).trans
        ((mulHeight_le_projectiveTupleHeight p.val j.1).trans p.property)⟩
  have hencode : Function.Injective encode := by
    intro p q hpq
    apply Subtype.ext
    funext i
    apply normalizedCoordinates_injective
    funext j
    exact congrArg (fun f => (f ⟨i, j⟩).val) hpq
  let : Finite S := Finite.of_injective encode hencode
  let : Fintype S := Fintype.ofFinite S
  refine ⟨Set.toFinite _, ?_⟩
  have hcard : S.ncard ≤ T.ncard ^ d := by
    simpa [Fintype.card_pi, d] using Fintype.card_le_of_injective encode hencode
  calc
    (S.ncard : ℝ) ≤ (T.ncard : ℝ) ^ d := by exact_mod_cast hcard
    _ ≤ (C * B ^ M) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) (hcount B hB) _
    _ = C ^ d * B ^ (M * d) := by rw [mul_pow, pow_mul]

/-- A sufficiently large inverse power of the product height is summable over all
tuples of rational projective points, including tuples with no factors. -/
theorem summable_projectiveTupleHeight_rpow (K : Type*) [Field K] [NumberField K]
    {I : Type*} [Fintype I] (J : I → Type*) [∀ i, Fintype (J i)] :
    ∃ d₀ : ℝ, 0 ≤ d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      Summable (fun p : ∀ i, Projectivization K (J i → K) => projectiveTupleHeight p ^ (-d)) := by
  obtain ⟨C, M, h⟩ := projectiveTupleHeight_count K J
  refine ⟨(M : ℝ) + 2, by positivity, fun d hd => ?_⟩
  exact summable_rpow_of_polynomial_height_count _ one_le_projectiveTupleHeight
    (fun B hB => (h B hB).1) (fun B hB => (h B hB).2) hd

/-- A sufficiently large inverse power of the multiplicative Weil height is summable
over all rational points of a single finite-dimensional projective space. -/
theorem summable_projectivization_mulHeight_rpow (K : Type*) [Field K] [NumberField K]
    (ι : Type*) [Fintype ι] :
    ∃ d₀ : ℝ, 0 ≤ d₀ ∧ ∀ d : ℝ, d₀ ≤ d →
      Summable (fun p : Projectivization K (ι → K) => p.mulHeight ^ (-d)) := by
  obtain ⟨d₀, hd₀, h⟩ := summable_projectiveTupleHeight_rpow K (fun _ : Unit => ι)
  refine ⟨d₀, hd₀, fun d hd => ?_⟩
  let f (p : Projectivization K (ι → K)) : Unit → Projectivization K (ι → K) := fun _ => p
  have hf : Function.Injective f := fun _ _ h => congrFun h ()
  simpa [f, projectiveTupleHeight, Function.comp_def] using (h d hd).comp_injective hf

end Langlands.Global
