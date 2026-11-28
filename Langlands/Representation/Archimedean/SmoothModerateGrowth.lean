import Langlands.Representation.Archimedean.BanachModerateGrowth
import Langlands.Representation.Archimedean.SmoothUnitAction

/-! # Moderate growth in the genuine derivative topology -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

private theorem norm_prod_nonneg {A : Type*} [SeminormedAddCommGroup A] (s : List A) :
    0 ≤ (s.map (fun X => ‖X‖)).prod :=
  List.prod_nonneg (by simp)

section Units

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

private theorem wordSeminormFamily_append_singleton (s : List A) (X : A) (v : D) :
    wordSeminormFamily 𝓜 R (s ++ [X]) v = wordSeminormFamily 𝓜 R s (operator 𝓜 R X v) := by
  simp only [wordSeminormFamily_apply, ← derivativeCoordinates_apply, derivativeCoordinates_operator]

variable [FiniteDimensional ℝ A]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ A)

/-- Iterated basis seminorms, weighted by the norms of the real basis coordinate maps. -/
def wordOrderSeminorm : ℕ → Seminorm ℂ D
  | 0 => wordSeminormFamily 𝓜 R []
  | k + 1 => ∑ i, ‖(b.coord i).toContinuousLinearMap‖₊ •
      (wordOrderSeminorm k).comp (operator 𝓜 R (b i))

private theorem wordOrderSeminorm_succ_apply (k : ℕ) (v : D) :
    wordOrderSeminorm R b (k + 1) v = ∑ i, ‖(b.coord i).toContinuousLinearMap‖ *
      wordOrderSeminorm R b k (operator 𝓜 R (b i) v) := by
  simp only [wordOrderSeminorm, FunLike.coe_sum, Finset.sum_apply, smul_apply,
    Seminorm.comp_apply, NNReal.smul_def, coe_nnnorm, smul_eq_mul]

theorem continuous_wordOrderSeminorm (k : ℕ) : Continuous (wordOrderSeminorm R b k) := by
  induction k with
  | zero => exact (derivativeCLM 𝓜 R []).continuous.norm
  | succ k ih =>
      change Continuous (fun v : D => wordOrderSeminorm R b (k + 1) v)
      simp_rw [wordOrderSeminorm_succ_apply]
      exact continuous_finsetSum _ fun i _ => continuous_const.mul
        (ih.comp (continuous_operator 𝓜 R (b i)))

private theorem wordOrderSeminorm_operator_le (k : ℕ) (X : A) (v : D) :
    wordOrderSeminorm R b k (operator 𝓜 R X v) ≤ ‖X‖ * wordOrderSeminorm R b (k + 1) v := by
  let p := wordOrderSeminorm R b k
  rw [operator_eq_sum_basis R b, wordOrderSeminorm_succ_apply, Finset.mul_sum]
  refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)
  change p (b.coord i X • operator 𝓜 R (b i) v) ≤ _
  have he := map_smul_eq_mul (p.restrictScalars ℝ) (b.coord i X) (operator 𝓜 R (b i) v)
  change p (b.coord i X • operator 𝓜 R (b i) v) =
    ‖b.coord i X‖ * p (operator 𝓜 R (b i) v) at he
  rw [he, ← mul_assoc, mul_comm ‖X‖]
  exact mul_le_mul_of_nonneg_right ((b.coord i).toContinuousLinearMap.le_opNorm X)
    (apply_nonneg p _)

/-- A word of order `k` is bounded by the product of the norms of its directions and
one continuous seminorm of order `k`. -/
theorem wordSeminormFamily_le_wordOrderSeminorm (s : List A) (v : D) :
    wordSeminormFamily 𝓜 R s v ≤ (s.map (fun X => ‖X‖)).prod * wordOrderSeminorm R b s.length v := by
  induction s using List.reverseRecOn generalizing v with
  | nil => simp [wordOrderSeminorm]
  | append_singleton s X ih =>
      rw [wordSeminormFamily_append_singleton, List.map_append, List.map_singleton, List.prod_append,
        List.prod_singleton, List.length_append, List.length_singleton, mul_assoc]
      exact (ih _).trans (mul_le_mul_of_nonneg_left
        (wordOrderSeminorm_operator_le R b s.length X v) (norm_prod_nonneg s))

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
private theorem norm_prod_inverseConjugation_le (g : Aˣ) (s : List A) :
    ((s.map (inverseConjugationCLM g)).map (fun X => ‖X‖)).prod ≤
      (unitHeight g ^ 2) ^ s.length * (s.map (fun X => ‖X‖)).prod := by
  have hh := zero_le_one.trans (one_le_unitHeight g)
  have hconj (X : A) : ‖inverseConjugationCLM g X‖ ≤ unitHeight g ^ 2 * ‖X‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg X))
    rw [pow_two]
    exact (norm_inverseConjugationCLM_le g).trans
      (mul_le_mul (norm_inv_le_unitHeight g) (norm_val_le_unitHeight g) (norm_nonneg _) hh)
  induction s with
  | nil => simp
  | cons X s ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      calc
        _ ≤ (unitHeight g ^ 2 * ‖X‖) *
            ((unitHeight g ^ 2) ^ s.length * (s.map (fun Y => ‖Y‖)).prod) :=
          mul_le_mul (hconj X) ih (norm_prod_nonneg (s.map (inverseConjugationCLM g))) (by positivity)
        _ = _ := by ring

/-- A bound on the Banach operator at a given unit gives the corresponding bound for an
individual word of the translated smooth vector. -/
theorem wordSeminormFamily_representation_le (s : List A) (g : Aˣ) (v : D)
    {C : ℝ} {d : ℕ} (hC : 0 ≤ C) (hg : ‖R g‖ ≤ C * unitHeight g ^ d) :
    wordSeminormFamily 𝓜 R s (representation 𝓜 R g v) ≤
      unitHeight g ^ (d + 2 * s.length) *
        (C * (s.map (fun X => ‖X‖)).prod * wordOrderSeminorm R b s.length v) := by
  have hh := zero_le_one.trans (one_le_unitHeight g)
  let t := s.map (inverseConjugationCLM g)
  have hw := wordSeminormFamily_le_wordOrderSeminorm R b t v
  rw [show t.length = s.length by simp [t]] at hw
  simp only [wordSeminormFamily_apply, ← derivativeCoordinates_apply] at hw ⊢
  rw [derivativeCoordinates_representation_units]
  calc
    _ ≤ ‖R g‖ * ‖derivativeCoordinates 𝓜 R v t‖ := (R g).le_opNorm _
    _ ≤ (C * unitHeight g ^ d) *
        ((t.map (fun X => ‖X‖)).prod * wordOrderSeminorm R b s.length v) :=
      mul_le_mul hg hw (norm_nonneg _) (mul_nonneg hC (pow_nonneg hh _))
    _ ≤ (C * unitHeight g ^ d) * ((unitHeight g ^ 2) ^ s.length *
          (s.map (fun X => ‖X‖)).prod * wordOrderSeminorm R b s.length v) := by
      gcongr
      exact norm_prod_inverseConjugation_le g s
    _ = _ := by rw [pow_add, pow_mul]; ring

/-- A polynomial bound for the original operator norm gives a polynomial bound on each
continuous seminorm of the genuine smooth action in terms of another continuous seminorm. -/
theorem exists_seminorm_le_unitHeight_pow_of_norm_bound
    {C : ℝ} {d : ℕ} (hC : 0 ≤ C) (hg : ∀ g : Aˣ, ‖R g‖ ≤ C * unitHeight g ^ d)
    (p : Seminorm ℂ D) (hp : Continuous p) :
    ∃ (k : ℕ) (q : Seminorm ℂ D), Continuous q ∧
      ∀ (g : Aˣ) (v : D), p (representation 𝓜 R g v) ≤ unitHeight g ^ k * q v := by
  classical
  obtain ⟨S, c, -, hpc⟩ := Seminorm.bound_of_continuous
    (withSeminorms_wordSeminormFamily 𝓜 R) p hp
  let b := Module.finBasis ℝ A
  let k := d + 2 * S.sup List.length
  let weight (s : List A) : ℝ≥0 := ⟨C * (s.map (fun X => ‖X‖)).prod,
    mul_nonneg hC (norm_prod_nonneg s)⟩
  let Q (s : List A) : Seminorm ℂ D := weight s • wordOrderSeminorm R b s.length
  have hQ (s : List A) (v : D) : Q s v = (weight s : ℝ) * wordOrderSeminorm R b s.length v := by
    simp only [Q, smul_apply, NNReal.smul_def, smul_eq_mul]
  let q : Seminorm ℂ D := c • ∑ s ∈ S, Q s
  have hq (v : D) : q v = (c : ℝ) * ∑ s ∈ S, Q s v := by
    simp only [q, smul_apply, NNReal.smul_def, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply]
  refine ⟨k, q, ?_, fun g v => ?_⟩
  · change Continuous (fun v : D => q v)
    simp_rw [hq, hQ]
    exact continuous_const.mul (continuous_finsetSum S fun s _ => continuous_const.mul
      (continuous_wordOrderSeminorm R b s.length))
  · have hh := one_le_unitHeight (A := A) g
    have hword (s : List A) (hs : s ∈ S) :
        wordSeminormFamily 𝓜 R s (representation 𝓜 R g v) ≤ unitHeight g ^ k * Q s v := by
      rw [hQ]
      change _ ≤ unitHeight g ^ k *
        (C * (s.map (fun X => ‖X‖)).prod * wordOrderSeminorm R b s.length v)
      refine (wordSeminormFamily_representation_le R b s g v hC (hg g)).trans ?_
      have hlen : s.length ≤ S.sup List.length := Finset.le_sup hs
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hh (by dsimp [k]; omega))
        (mul_nonneg (mul_nonneg hC (norm_prod_nonneg s)) (apply_nonneg _ _))
    have hs : (S.sup (wordSeminormFamily 𝓜 R)) (representation 𝓜 R g v) ≤
        unitHeight g ^ k * ∑ s ∈ S, Q s v := by
      apply Seminorm.finset_sup_apply_le (mul_nonneg (pow_nonneg (zero_le_one.trans hh) _)
        (Finset.sum_nonneg fun s _ => apply_nonneg _ _))
      intro s hs
      exact (hword s hs).trans (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun t => Q t v) (fun t _ => apply_nonneg (Q t) v) hs)
        (pow_nonneg (zero_le_one.trans hh) _))
    have hb := Seminorm.le_def.mp hpc (representation 𝓜 R g v)
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at hb
    calc
      _ ≤ (c : ℝ) * (S.sup (wordSeminormFamily 𝓜 R)) (representation 𝓜 R g v) := hb
      _ ≤ (c : ℝ) * (unitHeight g ^ k * ∑ s ∈ S, Q s v) :=
        mul_le_mul_of_nonneg_left hs c.coe_nonneg
      _ = _ := by rw [hq]; ring

end Units

section GeneralLinear

variable (F : Type*) [RCLike F] (n : ℕ)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (R : Langlands.GeneralLinear n F →* (E →L[ℂ] E))

local notation "Mat" => Matrix (Fin n) (Fin n) F
local notation "𝓜" => matrixModel F n
local notation "D" => DerivativeSmoothVectors 𝓜 R

/-- The action on the genuine smooth-vector topology has moderate growth. For each
continuous seminorm there is a continuous seminorm and a nonnegative integer exponent
bounding all translates by a power of the unit height. -/
theorem exists_seminorm_le_unitHeight_pow (hR : IsContinuousRepresentation R)
    (p : Seminorm ℂ D) (hp : Continuous p) :
    ∃ (k : ℕ) (q : Seminorm ℂ D), Continuous q ∧
      ∀ g : Langlands.GeneralLinear n F, ∀ v : D,
        p (representation 𝓜 R g v) ≤ unitHeight (A := Mat) g ^ k * q v := by
  classical
  obtain ⟨C, d, hC, hg⟩ := exists_norm_le_unitHeight_pow F n R hR
  exact exists_seminorm_le_unitHeight_pow_of_norm_bound R hC hg p hp

end GeneralLinear

end Langlands.Archimedean.DerivativeSmoothVectors
