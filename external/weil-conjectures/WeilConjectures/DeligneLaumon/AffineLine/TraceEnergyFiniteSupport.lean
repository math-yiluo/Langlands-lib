/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.FourierWeight
public import WeilConjectures.WeilSheaf.LocalFrobenius

/-!
# Squared traces of a Weil complex supported at finitely many closed points

Let `K` be a Weil complex on `X₀`, of finite type over `k₀`, supported at finitely many closed
points, such that every eigenvalue `α` of the local Frobenius `F_x` on every stalk `𝓗ʲ(K)_x̄`
satisfies `|ι α| ≤ q_x^{a/2}`. Then the trace energies grow at most like `q^{na}`, so that the
`L²`-weight parameter of `K` is at most `a - 1`.

## Main statements

- `AlgebraicGeometry.WeilComplex.l2Weight_le_of_traceEnergy_le`: an energy bound
  `S_n(K) ≤ C q^{nB}` gives `‖K‖ ≤ B - 1`.
- `AlgebraicGeometry.WeilComplex.exists_traceEnergy_le_of_finite_support`: `S_n(K) ≤ C q^{na}`.
- `AlgebraicGeometry.WeilComplex.l2Weight_le_of_finite_support`: `‖K‖ ≤ a - 1`.

## Implementation details

For the energy bound, at an `𝔽_{qⁿ}`-point `y` over a closed point `x` the trace `t_K(y)` is the
alternating sum of the traces of `F_x^{n / deg x}` on the stalks `𝓗ʲ(K)_x̄`, hence
`|ι t_K(y)| ≤ N q^{na/2}` with `N` the sum over `j` of the ranks of the stalks, and it vanishes
unless `x` lies in the support; over each closed point `x` there are at most `deg x` such
points `y`.
-/

@[expose] public section

universe u

open CategoryTheory Filter Topology

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace energy bound `S_m(K) ≤ C q^{mB}` for `m ≥ 1` bounds the `L²`-weight parameter of
a Weil complex: `‖K‖ ≤ B - 1`. -/
theorem l2Weight_le_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    {C B : ℝ} (hS : ∀ n : ℕ, 1 ≤ n → K.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B)) :
    K.l2Weight ι ≤ ((B - 1 : ℝ) : EReal) := by
  refine iSup₂_le fun β hβ ↦ EReal.coe_le_coe_iff.2 (not_lt.1 fun hlt ↦ hβ.ne' ?_)
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  have hq0 : (0 : ℝ) < Nat.card k₀ := by linarith
  have hr1 : (Nat.card k₀ : ℝ) ^ (B - (β + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hlim : Tendsto (fun m : ℕ ↦ ENNReal.ofReal
      (C * ((Nat.card k₀ : ℝ) ^ (B - (β + 1))) ^ m)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1).const_mul C
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_).limsup_eq
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  calc K.traceEnergy ι m ≤ C * (Nat.card k₀ : ℝ) ^ ((m : ℝ) * B) := hS m hm
    _ = C * ((Nat.card k₀ : ℝ) ^ (B - (β + 1))) ^ m *
        (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
      congr 2
      ring

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Let `K` be a Weil complex on `X₀`, of finite type over `k₀`, supported at finitely many
closed points, such that every eigenvalue `α` of the local Frobenius `F_x` on every stalk
`𝓗ʲ(K)_x̄` satisfies `|ι α| ≤ q_x^{a/2}`. Then there is a constant `C` with
`S_n(K) ≤ C q^{na}` for all `n`. -/
theorem exists_traceEnergy_le_of_finite_support (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (hK : {x : X.finitePoints | ∃ j : ℤ, Nontrivial (K.stalk j x).carrier}.Finite) {a : ℝ}
    (ha : ∀ (j : ℤ) (x : X.finitePoints),
      (K.stalk j x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) a) :
    ∃ C : ℝ, ∀ n : ℕ, K.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * a) := by
  classical
  obtain ⟨T, hT⟩ := K.exists_finset_isZero_homologySheaf
  set B := hK.toFinset
  let N : ℕ := ∑ j ∈ T, B.sup fun x ↦ Module.finrank (PadicAlgCl l) (K.stalk j x).carrier
  let d : ℕ := ∑ x ∈ B, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  refine ⟨d * N ^ 2, fun n ↦ ?_⟩
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have := (X ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints (FiniteField.galoisExtension k₀ n)
  let : Fintype ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ n)) := Fintype.ofFinite _
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  set Q : ℝ := ((Nat.card k₀ : ℝ) ^ (a / 2)) ^ n
  have hQ : 0 ≤ Q := by positivity
  -- the trace of `K` at `y` is bounded by the ranks of the stalks at the closed point under `y`
  have hnorm (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
      ‖ι (K.traceFunction n y)‖ ≤ (∑ j ∈ T, Module.finrank (PadicAlgCl l)
        (K.stalk j (WeilSheaf.finitePointOfFieldPoint y)).carrier : ℕ) * Q := by
    rw [K.traceFunction_eq_sum T hT, map_sum, Nat.cast_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [map_zsmul]
    obtain h | h := Int.units_eq_one_or j.negOnePow <;>
    · simp only [h, Units.val_one, Units.val_neg, one_smul, neg_smul, norm_neg]
      exact WeilSheaf.norm_map_traceFunction_le (fun x ↦ ha j x) n y
  -- the trace of `K` vanishes away from the support
  have hzero (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n))
      (hy : WeilSheaf.finitePointOfFieldPoint y ∉ B) : ‖ι (K.traceFunction n y)‖ ^ 2 = 0 := by
    refine pow_eq_zero_iff two_ne_zero |>.2 (le_antisymm ((hnorm y).trans_eq ?_) (norm_nonneg _))
    rw [Finset.sum_eq_zero fun j _ ↦ ?_, Nat.cast_zero, zero_mul]
    have : Subsingleton (K.stalk j (WeilSheaf.finitePointOfFieldPoint y)).carrier :=
      not_nontrivial_iff_subsingleton.1 fun h ↦ hy (hK.mem_toFinset.2 ⟨j, h⟩)
    exact Module.finrank_zero_of_subsingleton
  -- each term over the support is at most `N² q^{na}`
  have hterm (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n))
      (hy : WeilSheaf.finitePointOfFieldPoint y ∈ B) :
      ‖ι (K.traceFunction n y)‖ ^ 2 ≤ (N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * a) := by
    have hN : (∑ j ∈ T, Module.finrank (PadicAlgCl l)
        (K.stalk j (WeilSheaf.finitePointOfFieldPoint y)).carrier : ℕ) ≤ N :=
      Finset.sum_le_sum fun j _ ↦ Finset.le_sup (f := fun x ↦ Module.finrank (PadicAlgCl l)
        (K.stalk j x).carrier) hy
    have hpow : Q * Q = (Nat.card k₀ : ℝ) ^ ((n : ℝ) * a) := by
      rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hq]
      congr 1
      push_cast
      ring
    calc ‖ι (K.traceFunction n y)‖ ^ 2 ≤ ((N : ℝ) * Q) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ((hnorm y).trans (by gcongr)) 2
      _ = _ := by rw [mul_pow, sq Q, hpow]
  -- there are at most `d` points over the support
  set s := Finset.univ.filter fun y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
    (FiniteField.galoisExtension k₀ n) ↦ WeilSheaf.finitePointOfFieldPoint y ∈ B
  have hcard : s.card ≤ d := by
    rw [Finset.card_eq_sum_card_fiberwise (s := s) (f := WeilSheaf.finitePointOfFieldPoint)
      (t := B)
      fun y hy ↦ (Finset.mem_filter.1 hy).2]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    calc _ ≤ Nat.card {p : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ n) // p.1.base (IsLocalRing.closedPoint _) = x.1} := by
          rw [← Nat.card_eq_finsetCard]
          refine Nat.card_le_card_of_injective (fun p ↦ ⟨p.1, congrArg Subtype.val
            (Finset.mem_filter.1 p.2).2⟩) fun p p' h ↦
              Subtype.ext (by simpa using congrArg Subtype.val h)
      _ ≤ _ := (X ↘ Spec (CommRingCat.of k₀)).card_fieldPoints_base_eq_le _ x.2
  rw [traceEnergy, finsum_eq_sum_of_fintype, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y ↦ WeilSheaf.finitePointOfFieldPoint y ∈ B),
    Finset.sum_eq_zero (s := Finset.univ.filter _) fun y hy ↦ hzero y (Finset.mem_filter.1 hy).2,
    add_zero]
  calc ∑ y ∈ s, ‖ι (K.traceFunction n y)‖ ^ 2
      ≤ ∑ _y ∈ s, (N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * a) :=
        Finset.sum_le_sum fun y hy ↦ hterm y (Finset.mem_filter.1 hy).2
    _ = s.card * ((N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * a)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d * ((N : ℝ) ^ 2 * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * a)) := by
        gcongr
    _ = _ := by ring

/-- Let `K` be a Weil complex on `X₀`, of finite type over `k₀`, supported at finitely many
closed points, such that every eigenvalue `α` of the local Frobenius `F_x` on every stalk
`𝓗ʲ(K)_x̄` satisfies `|ι α| ≤ q_x^{a/2}`. Then `‖K‖ ≤ a - 1`. -/
theorem l2Weight_le_of_finite_support (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (hK : {x : X.finitePoints | ∃ j : ℤ, Nontrivial (K.stalk j x).carrier}.Finite) {a : ℝ}
    (ha : ∀ (j : ℤ) (x : X.finitePoints),
      (K.stalk j x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) a) :
    K.l2Weight ι ≤ ((a - 1 : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := K.exists_traceEnergy_le_of_finite_support ι hK ha
  exact K.l2Weight_le_of_traceEnergy_le ι fun n _ ↦ hC n

end AlgebraicGeometry.WeilComplex
