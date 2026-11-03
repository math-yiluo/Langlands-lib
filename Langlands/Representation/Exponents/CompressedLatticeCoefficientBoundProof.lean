import Langlands.Representation.Exponents.CompressedLatticeCoefficientBoundStatement
import Langlands.Representation.Exponents.StrictCartanCoefficientBoundProof

/-! # Finite lattice coefficient bounds from compression spectra -/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uG uV uI

namespace CompressedLatticeBound

/-- Multiplicative maps from finite natural-coordinate lattices are controlled
by power bounds on their coordinate generators. -/
theorem endNorm_le_prod_of_pow_bounds
    {I : Type uI} [Fintype I] [DecidableEq I]
    {W : Type uV} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : (I → ℕ) → Module.End ℂ W)
    (hadd : ∀ a b, f (a + b) = f a * f b)
    (c a : I → ℝ)
    (hbound : ∀ i k, EndomorphismBound.endNorm (f (Pi.single i 1) ^ k) ≤ c i * a i ^ k)
    (n : I → ℕ) :
    EndomorphismBound.endNorm (f n) ≤
      (EndomorphismBound.endNorm (f 0) * ∏ i, c i) * ∏ i, a i ^ n i := by
  have hpow : ∀ i k, f (Pi.single i k) = f (Pi.single i 1) ^ k * f 0 := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      have he : (Pi.single i (k + 1) : I → ℕ) = Pi.single i 1 + Pi.single i k := by
        rw [← Pi.single_add, Nat.add_comm k 1]
      rw [he, hadd, ih, ← mul_assoc, ← pow_succ']
  have key : ∀ S : Finset I,
      EndomorphismBound.endNorm (f (∑ i ∈ S, Pi.single i (n i))) ≤
        EndomorphismBound.endNorm (f 0) * ∏ i ∈ S, (c i * a i ^ n i) := by
    intro S
    induction S using Finset.induction with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, hadd]
      have h1 := hbound i (n i)
      have h2 := EndomorphismBound.endNorm_nonneg (f (∑ j ∈ S, Pi.single j (n j)))
      have hpos : 0 ≤ c i * a i ^ n i := (EndomorphismBound.endNorm_nonneg _).trans h1
      rw [hpow, mul_assoc, ← hadd, zero_add]
      calc
        _ ≤ EndomorphismBound.endNorm (f (Pi.single i 1) ^ n i) *
            EndomorphismBound.endNorm (f (∑ j ∈ S, Pi.single j (n j))) :=
          EndomorphismBound.endNorm_mul_le _ _
        _ ≤ (c i * a i ^ n i) *
            (EndomorphismBound.endNorm (f 0) * ∏ j ∈ S, (c j * a j ^ n j)) :=
          mul_le_mul h1 ih h2 hpos
        _ = _ := by ring
  have h := key Finset.univ
  rw [Finset.univ_sum_single, Finset.prod_mul_distrib, ← mul_assoc] at h
  exact h

/-- Strict bounds on generator eigenvalues give strict product-exponential
bounds for every matrix coefficient of a finite lattice of operators. -/
theorem exists_apply_le_prod
    {I : Type uI} [Fintype I] [DecidableEq I]
    {W : Type uV} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : (I → ℕ) → Module.End ℂ W)
    (hadd : ∀ a b, f (a + b) = f a * f b)
    (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (hev : ∀ i (μ : ℂ) (x : W), x ≠ 0 → f (Pi.single i 1) x = μ • x → ‖μ‖ < s i)
    (v : W) (φ : Module.Dual ℂ W) :
    ∃ a : I → ℝ, (∀ i, 0 < a i ∧ a i < s i) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ, ‖φ (f n v)‖ ≤ C * ∏ i, a i ^ n i := by
  choose r hr0 hrs hr using fun i =>
    StrictCartanBound.exists_eigenvalue_bound_lt (f (Pi.single i 1)) (hs i) (hev i)
  let a : I → ℝ := fun i => (r i + s i) / 2
  have hra : ∀ i, r i < a i := fun i => by dsimp [a]; linarith [hrs i]
  have has : ∀ i, a i < s i := fun i => by dsimp [a]; linarith [hrs i]
  have ha0 : ∀ i, 0 < a i := fun i => (hr0 i).trans_lt (hra i)
  choose c hc using fun i =>
    EndomorphismBound.exists_endNorm_pow_le (f (Pi.single i 1)) (hr0 i) (hra i) (hr i)
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    have h := hc i 0
    rw [pow_zero, pow_zero, mul_one] at h
    exact (EndomorphismBound.endNorm_nonneg _).trans h
  obtain ⟨D, hD0, hD⟩ := EndomorphismBound.exists_apply_le_endNorm φ v
  let E := EndomorphismBound.endNorm (f 0) * ∏ i, c i
  have hE0 : 0 ≤ E := mul_nonneg (EndomorphismBound.endNorm_nonneg _)
    (Finset.prod_nonneg fun i _ => hc0 i)
  refine ⟨a, fun i => ⟨ha0 i, has i⟩, D * E + 1, by positivity, fun n => ?_⟩
  have hp0 : 0 ≤ ∏ i, a i ^ n i := Finset.prod_nonneg fun i _ => (pow_pos (ha0 i) _).le
  calc
    ‖φ (f n v)‖ ≤ D * EndomorphismBound.endNorm (f n) := hD _
    _ ≤ D * (E * ∏ i, a i ^ n i) :=
      mul_le_mul_of_nonneg_left (endNorm_le_prod_of_pow_bounds f hadd c a hc n) hD0
    _ ≤ (D * E + 1) * ∏ i, a i ^ n i := by nlinarith

end CompressedLatticeBound

/-- Strict spectra of an actual multiplicative compressed lattice bound its
original smooth coefficients. -/
theorem compressedLatticeCoefficientBound :
    CompressedLatticeCoefficientBoundStatement.{uG, uV, uI} := by
  intro G _ _ _ V _ _ I _ _ ρ hρ K hK N M Nbar hfactor τ hup hlow hmid s hs hev v φ hφ
  let W := fixedVectors ρ K.toSubgroup
  have : FiniteDimensional ℂ W := hρ.2 K
  let f : (I → ℕ) → Module.End ℂ W :=
    fun n => Jacquet.compressedAction ρ hρ.1 K hK (τ (.ofAdd n))
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    change Jacquet.compressedAction ρ hρ.1 K hK (τ (.ofAdd a * .ofAdd b)) = _
    rw [map_mul]
    exact Jacquet.compressedAction_mul_of_factor ρ hρ.1 K hK N M Nbar hfactor _ _
      (hup a) (hlow b) (hmid b)
  obtain ⟨a, ha, C, hC, hbound⟩ := CompressedLatticeBound.exists_apply_le_prod
    f hadd s hs hev v (φ.comp W.subtype)
  refine ⟨a, ha, C, hC, fun n => ?_⟩
  rw [StrictCartanBound.dual_apply_eq_compressedAction ρ hρ.1 K hK φ hφ]
  exact hbound n

end Langlands
