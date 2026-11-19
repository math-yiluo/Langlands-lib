import Langlands.Representation.Archimedean.RealOrthogonalUncertainty
import Langlands.Representation.Archimedean.RealTailMultiplierPolynomial
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # One-sided Fourier lifting on an adjacent weight string -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealAdjacentWeightStringLifting

open Complex Polynomial RealOrthogonalUncertainty RealTailMultiplierPolynomial

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}

private theorem proj_scaled_apply (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (i : ℤ) (v : W) :
    π i ((-I • b) v) = (-I / 2 : ℂ) •
      ((b - I • c) (π (i - 1) v) + (b + I • c) (π (i + 1) v)) := by
  rw [LinearMap.smul_apply, map_smul]
  conv_lhs => rw [eq_half_raise_add_lower (b := b) (c := c)]
  rw [LinearMap.smul_apply, map_smul, LinearMap.add_apply, map_add,
    hM.proj_apply_of_lie (lie_raise hab hca), hM.proj_apply_of_lie (lie_lower hab hca),
    sub_neg_eq_add, smul_smul]
  simp only [div_eq_mul_inv, one_mul]

private theorem proj_pow_top (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (v : W) (m : ℤ)
    (hv : ∀ i : ℤ, m < i → π i v = 0) (d : ℕ) :
    π (m + d) (((-I • b) ^ d) v) =
        (-I / 2 : ℂ) ^ d • ((b - I • c) ^ d) (π m v) ∧
      ∀ i : ℤ, m + d < i → π i (((-I • b) ^ d) v) = 0 := by
  induction d with
  | zero => simpa using hv
  | succ d ih =>
    constructor
    · rw [pow_succ' (-I • b), Module.End.mul_apply, proj_scaled_apply hab hca hM,
        show m + (d + 1 : ℕ) - 1 = m + d by omega,
        ih.1, ih.2 _ (by omega), map_zero, add_zero, map_smul, smul_smul,
        pow_succ' (-I / 2 : ℂ), pow_succ' (b - I • c), Module.End.mul_apply]
    · intro i hi
      rw [pow_succ' (-I • b), Module.End.mul_apply, proj_scaled_apply hab hca hM,
        ih.2 _ (by omega), ih.2 _ (by omega), map_zero, map_zero, add_zero, smul_zero]

/-- The top possible output of a polynomial in the adjacent rotation is obtained
by raising the top input once per degree. -/
theorem proj_aeval_top (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) (v : W) (m : ℤ)
    (hv : ∀ i : ℤ, m < i → π i v = 0) (Q : ℂ[X]) :
    π (m + Q.natDegree) (aeval (-I • b) Q v) =
      (Q.leadingCoeff * (-I / 2 : ℂ) ^ Q.natDegree) •
        ((b - I • c) ^ Q.natDegree) (π m v) := by
  classical
  rw [aeval_eq_sum_range, LinearMap.sum_apply, map_sum, Finset.sum_eq_single Q.natDegree]
  · rw [LinearMap.smul_apply, map_smul, (proj_pow_top hab hca hM v m hv _).1, smul_smul,
      coeff_natDegree]
  · intro d hd hne
    have hlt : d < Q.natDegree := by
      have := Finset.mem_range.mp hd
      omega
    rw [LinearMap.smul_apply, map_smul,
      (proj_pow_top hab hca hM v m hv d).2 _ (by omega), smul_zero]
  · simp

private theorem exists_top_mode (hM : IsModeDecomposition a π S) {v : W} (hv : v ≠ 0) :
    ∃ m ∈ S, π m v ≠ 0 ∧ ∀ i : ℤ, m < i → π i v = 0 := by
  classical
  let T := S.filter fun i => π i v ≠ 0
  have hT : T.Nonempty := by
    by_contra h
    apply hv
    rw [← hM.sum_apply v]
    exact Finset.sum_eq_zero fun i hi => by
      by_contra! hn
      exact h ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩
  let m := T.max' hT
  have hm := Finset.mem_filter.mp (T.max'_mem hT)
  refine ⟨m, hm.1, hm.2, fun i hi => ?_⟩
  by_cases hS : i ∈ S
  · by_contra! h
    exact hi.not_ge (T.le_max' i (Finset.mem_filter.mpr ⟨hS, h⟩))
  · rw [hM.eq_zero i hS, LinearMap.zero_apply]

private theorem raise_pow_ne_zero (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) {J : ℤ}
    (hraise : ∀ (i : ℤ), i < J → ∀ v : W, (b - I • c) (π i v) = 0 → π i v = 0)
    {v : W} {m : ℤ} (hv : π m v ≠ 0) (d : ℕ) (hd : m + d ≤ J) :
    ((b - I • c) ^ d) (π m v) ≠ 0 := by
  have himage : ∀ k : ℕ, π (m + k) (((b - I • c) ^ k) (π m v)) =
      ((b - I • c) ^ k) (π m v) := by
    intro k
    induction k with
    | zero => simp [hM.proj_apply_proj]
    | succ k ih =>
      rw [pow_succ' (b - I • c), Module.End.mul_apply, hM.proj_apply_of_lie (lie_raise hab hca),
        show m + (k + 1 : ℕ) - 1 = m + k by omega, ih]
  induction d with
  | zero => simpa using hv
  | succ d ih =>
    rw [pow_succ' (b - I • c), Module.End.mul_apply]
    intro hz
    have hs := hraise (m + d) (by omega) (((b - I • c) ^ d) (π m v))
    rw [himage] at hs
    exact ih (by omega) (hs hz)

private theorem proj_aeval_top_ne_zero (hab : a * b - b * a = c)
    (hca : c * a - a * c = b) (hM : IsModeDecomposition a π S) {J : ℤ}
    (hraise : ∀ (i : ℤ), i < J → ∀ v : W, (b - I • c) (π i v) = 0 → π i v = 0)
    {v : W} {m : ℤ} (hm : π m v ≠ 0) (hv : ∀ i : ℤ, m < i → π i v = 0)
    {Q : ℂ[X]} (hQ : Q ≠ 0) (hd : m + Q.natDegree ≤ J) :
    π (m + Q.natDegree) (aeval (-I • b) Q v) ≠ 0 := by
  rw [proj_aeval_top hab hca hM v m hv Q]
  exact smul_ne_zero
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hQ)
      (pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr I_ne_zero) (by norm_num))))
    (raise_pow_ne_zero hab hca hM hraise hm _ hd)

variable [FiniteDimensional ℂ W]

/-- On a weight string, any distinct adjacent eigenvalues suffice to interpolate
the same number of highest primary coordinates. -/
private theorem interpolate_top (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) {J : ℤ} (hbound : ∀ i ∈ S, i ≤ J)
    (hdim : ∀ i, Module.finrank ℂ (LinearMap.range (π i)) ≤ 1)
    (hraise : ∀ (i : ℤ), i < J → ∀ v : W, (b - I • c) (π i v) = 0 → π i v = 0)
    (T : Finset ℤ) (heig : ∀ j ∈ T, (-I • b).HasEigenvalue (j : ℂ))
    (P : ℂ[X]) (hroot : ∀ j ∈ T, P.eval (j : ℂ) = 0) (v : W) :
    ∃ w : W, aeval (-I • b) P w = 0 ∧
      ∀ i : ℤ, J - T.card < i → π i w = π i v := by
  classical
  let B : Module.End ℂ W := -I • b
  choose u hu using fun j : T => (heig j j.property).exists_hasEigenvector
  let U := Submodule.span ℂ (Set.range u)
  have hU : Module.finrank ℂ U = T.card := by
    have hli := B.eigenvectors_linearIndependent' (fun j : T => ((j : ℤ) : ℂ))
      (fun j k hjk => Subtype.ext (by
        change ((j : ℤ) : ℂ) = ((k : ℤ) : ℂ) at hjk
        exact_mod_cast hjk)) u hu
    simpa [U] using finrank_span_eq_card hli
  let Q : ℂ[X] := ∏ j ∈ T, (X - C (j : ℂ))
  have hQ : Q.Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (j : ℂ)
  have hdeg : Q.natDegree = T.card := by
    dsimp only [Q]
    rw [natDegree_prod_of_monic T (fun j : ℤ => X - C (j : ℂ))
      (fun j _ => monic_X_sub_C (j : ℂ))]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  have hkill {R : ℂ[X]} (hR : ∀ j ∈ T, R.eval (j : ℂ) = 0) :
      U ≤ LinearMap.ker (aeval B R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change u j ∈ LinearMap.ker (aeval B R)
    rw [LinearMap.mem_ker, Module.End.aeval_apply_of_hasEigenvector (show
        B.HasEigenvector (j : ℤ) (u j) from hu j),
      hR _ j.property, zero_smul]
  have hkillQ := hkill (R := Q) fun j hj => by
    dsimp only [Q]
    rw [eval_prod]
    apply Finset.prod_eq_zero hj
    simp
  let Top := Finset.Ioc (J - T.card) J
  let Coordinates := ∀ i : Top, LinearMap.range (π i)
  let F : U →ₗ[ℂ] Coordinates := LinearMap.pi fun i : Top =>
    (π i).rangeRestrict.domRestrict U
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra! hn
    have hne : (x : W) ≠ 0 := fun h => hn (Subtype.ext h)
    obtain ⟨m, hmS, hm, htop⟩ := exists_top_mode hM hne
    have hJ := hbound m hmS
    have hm' : m ≤ J - T.card := by
      by_contra! h
      let i : Top := ⟨m, Finset.mem_Ioc.mpr ⟨h, hJ⟩⟩
      exact hm (congrArg (fun y : Coordinates => (y i : W)) hx)
    have hnonzero := proj_aeval_top_ne_zero hab hca hM hraise hm htop hQ.ne_zero
      (by rw [hdeg]; omega)
    rw [LinearMap.mem_ker.mp (hkillQ x.property), map_zero] at hnonzero
    exact hnonzero rfl
  have hdim' : Module.finrank ℂ Coordinates ≤ T.card := by
    change Module.finrank ℂ (∀ i : Top, LinearMap.range (π i)) ≤ T.card
    rw [Module.finrank_pi_fintype]
    calc
      _ ≤ ∑ _ : Top, 1 := Finset.sum_le_sum fun i _ => hdim i
      _ = T.card := by simp [Top, Int.card_Ioc]
  have hfinrank : Module.finrank ℂ U = Module.finrank ℂ Coordinates := by
    apply le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
    rw [hU]
    exact hdim'
  let e := LinearEquiv.ofInjectiveOfFinrankEq F hinj hfinrank
  let y : Coordinates := fun i : Top => ⟨π i v, LinearMap.mem_range_self _ v⟩
  let w : U := e.symm y
  have hw : F w = y := e.apply_symm_apply y
  refine ⟨w, LinearMap.mem_ker.mp (hkill hroot w.property), fun i hi => ?_⟩
  by_cases hJ : i ≤ J
  · let j : Top := ⟨i, Finset.mem_Ioc.mpr ⟨hi, hJ⟩⟩
    exact congrArg (fun z : Coordinates => (z j : W)) hw
  · rw [hM.eq_zero _ (fun h => hJ (hbound _ h)), LinearMap.zero_apply, LinearMap.zero_apply]

private theorem tail_root {H k : ℕ} (hk : k < H) :
    (tailPolynomial H).eval ((2 * (k : ℤ) - (H : ℤ) + 1 : ℤ) : ℂ) = 0 := by
  rw [tailPolynomial_eval]
  push_cast
  rw [show (2 * (k : ℂ) - (H : ℂ) + 1 + (H : ℂ) - 1) / 2 = (k : ℂ) by ring,
    descPochhammer_eval_eq_prod_range]
  have h : ∏ x ∈ Finset.range H, ((k : ℂ) - (x : ℂ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hk) (sub_self _)
  rw [h, zero_div]

private theorem exists_tail_roots (H : ℕ) {J N : ℤ} (hN : 0 < N) (hNJ : N ≤ J) :
    ∃ T : Finset ℤ, T.card = min H (J - N + 1).toNat ∧
      ∀ j ∈ T, -J ≤ j ∧ j ≤ J ∧ (tailPolynomial H).eval (j : ℂ) = 0 := by
  let r := min H (J - N + 1).toNat
  let k₀ := max (0 : ℤ) (((H : ℤ) - J) / 2)
  let s : ℕ → ℤ := fun k => 2 * (k₀ + (k : ℤ)) - H + 1
  have hs : Function.Injective s := by
    intro k k' h
    dsimp [s] at h
    omega
  refine ⟨(Finset.range r).image s, by rw [Finset.card_image_of_injective _ hs, Finset.card_range], ?_⟩
  intro j hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  have hk' := Finset.mem_range.mp hk
  have hkH : k < H := lt_of_lt_of_le hk' (min_le_left ..)
  have hkJ : (k : ℤ) < J := by
    have := lt_of_lt_of_le hk' (min_le_right ..)
    omega
  have hk₀ : 0 ≤ k₀ := le_max_left _ _
  have hj₀ : -J ≤ s k := by
    have h := le_max_right (0 : ℤ) (((H : ℤ) - J) / 2)
    dsimp [s]
    omega
  have hlast : s k ≤ J ∧ k₀ + (k : ℤ) < H := by
    by_cases h : (H : ℤ) ≤ J + 1
    · have hzero : k₀ = 0 := max_eq_left (by omega)
      dsimp [s]
      omega
    · have hnonneg : 0 ≤ ((H : ℤ) - J) / 2 := by omega
      have heq : k₀ = ((H : ℤ) - J) / 2 := max_eq_right hnonneg
      dsimp [s]
      omega
  refine ⟨hj₀, hlast.1, ?_⟩
  have hnat : ((k₀ + (k : ℤ)).toNat : ℤ) = k₀ + (k : ℤ) := by omega
  have hK : (k₀ + (k : ℤ)).toNat < H := by omega
  simpa only [hnat, s] using tail_root hK

/-- A vector whose adjacent polynomial image has no modes at or above `N+H`
has the same modes at or above `N` as a vector in the polynomial kernel. -/
theorem exists_lift (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) {J : ℤ} (hbound : ∀ i ∈ S, i ≤ J)
    (hdim : ∀ i, Module.finrank ℂ (LinearMap.range (π i)) ≤ 1)
    (hraise : ∀ (i : ℤ), i < J → ∀ v : W, (b - I • c) (π i v) = 0 → π i v = 0)
    (heig : ∀ j : ℤ, -J ≤ j → j ≤ J → (-I • b).HasEigenvalue (j : ℂ))
    {N : ℤ} (hN : 0 < N) (H : ℕ) (v : W)
    (hv : ∀ i : ℤ, N + H ≤ i → π i (aeval (-I • b) (tailPolynomial H) v) = 0) :
    ∃ w : W, aeval (-I • b) (tailPolynomial H) w = 0 ∧
      ∀ i : ℤ, N ≤ i → π i w = π i v := by
  by_cases hNJ : N ≤ J
  · obtain ⟨T, hcard, hT⟩ := exists_tail_roots H hN hNJ
    obtain ⟨w, hw, htop⟩ := interpolate_top hab hca hM hbound hdim hraise T
      (fun j hj => heig j (hT j hj).1 (hT j hj).2.1)
      (tailPolynomial H) (fun j hj => (hT j hj).2.2) v
    refine ⟨w, hw, fun i hi => ?_⟩
    by_contra! hne
    let z := v - w
    have hz : π i z ≠ 0 := by
      dsimp only [z]
      rw [map_sub]
      exact sub_ne_zero.mpr (Ne.symm hne)
    have hzne : z ≠ 0 := fun h => hz (by rw [h, map_zero])
    obtain ⟨m, _, hm, htopz⟩ := exists_top_mode hM hzne
    have him : i ≤ m := le_of_not_gt (fun h => hz (htopz _ h))
    have hmJ : m ≤ J - T.card := le_of_not_gt fun h => hm (by simp [z, htop m h])
    have hcount : T.card = H := by
      rw [hcard, min_eq_left]
      omega
    have hQ : tailPolynomial H ≠ 0 := by
      cases H with
      | zero => simp [tailPolynomial]
      | succ H =>
        intro h
        have hh := tailPolynomial_natDegree H.succ
        rw [h, natDegree_zero] at hh
        omega
    have hne' := proj_aeval_top_ne_zero hab hca hM hraise hm htopz hQ
      (by rw [tailPolynomial_natDegree, ← hcount]; omega)
    have hmap : aeval (-I • b) (tailPolynomial H) z = aeval (-I • b) (tailPolynomial H) v := by
      dsimp only [z]
      rw [map_sub, hw, sub_zero]
    rw [tailPolynomial_natDegree, hmap, hv _ (by omega)] at hne'
    exact hne' rfl
  · refine ⟨0, map_zero _, fun i hi => ?_⟩
    rw [hM.eq_zero _ (fun h => hNJ (hi.trans (hbound _ h))), LinearMap.zero_apply,
      LinearMap.zero_apply]

end Langlands.Archimedean.RealAdjacentWeightStringLifting

namespace Langlands.Archimedean

open Complex Polynomial RealOrthogonalUncertainty RealTailMultiplierPolynomial

/-- One-sided lifting from high primary modes to the kernel of the polynomial
in the adjacent rotation, under the single-string hypotheses. -/
def RealAdjacentWeightStringLiftingStatement.{u} : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W],
    ∀ (a b c : Module.End ℂ W) (π : ℤ → Module.End ℂ W) (S : Finset ℤ),
    a * b - b * a = c → c * a - a * c = b → IsModeDecomposition a π S →
    ∀ J : ℤ, (∀ i ∈ S, i ≤ J) →
    (∀ i, Module.finrank ℂ (LinearMap.range (π i)) ≤ 1) →
    (∀ i < J, ∀ v : W, (b - I • c) (π i v) = 0 → π i v = 0) →
    (∀ j : ℤ, -J ≤ j → j ≤ J → (-I • b).HasEigenvalue (j : ℂ)) →
    ∀ N : ℤ, 0 < N → ∀ (H : ℕ) (v : W),
    (∀ i : ℤ, N + H ≤ i → π i (aeval (-I • b) (tailPolynomial H) v) = 0) →
    ∃ w : W, aeval (-I • b) (tailPolynomial H) w = 0 ∧
      ∀ i : ℤ, N ≤ i → π i w = π i v

theorem realAdjacentWeightStringLifting : RealAdjacentWeightStringLiftingStatement := by
  intro W _ _ _ a b c π S hab hca hM J hbound hdim hraise heig N hN H v hv
  exact RealAdjacentWeightStringLifting.exists_lift hab hca hM hbound hdim hraise heig hN H v hv

end Langlands.Archimedean
