import Langlands.LinearAlgebra.MatrixMinor
import Langlands.Representation.Archimedean.ChartIwasawaPower
import Langlands.Representation.Archimedean.JacquetKernel

/-!
# The Jacquet integral of a principal minor vector does not vanish
-/

noncomputable section

open MeasureTheory Matrix Finset

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace JacquetMinor

open MatrixMinor ChartIwasawaPower PartialSqIntegral MaximalParabolicIntegration
  ParabolicChartBound PartialJacquet JacquetDual JacquetKernel GramFormula Langlands.GeneralLinear
  PrincipalSeriesExtension

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-! ## Minor functions on `O(n)` -/

/-- The minor `κ ↦ det κ_{A,B}` on `O(n)`, as a complex function. -/
def minorFun (n : ℕ) (A B : Finset (Fin n)) (κ : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  ((minor (κ : Matrix (Fin n) (Fin n) ℝ) A B : ℝ) : ℂ)

variable {n : ℕ}

theorem continuous_minorFun (A B : Finset (Fin n)) : Continuous (minorFun n A B) :=
  Complex.continuous_ofReal.comp ((continuous_minor A B).comp continuous_subtype_val)

theorem minorFun_mul {A B : Finset (Fin n)} (hB : B.card = A.card)
    (κ k : Matrix.unitaryGroup (Fin n) ℝ) :
    minorFun n A B (κ * k) = ∑ C ∈ powersetCard A.card univ,
      ((minor (k : Matrix (Fin n) (Fin n) ℝ) C B : ℝ) : ℂ) * minorFun n A C κ := by
  unfold minorFun
  change ((minor ((κ : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ)) A B : ℝ) : ℂ) = _
  rw [minor_mul _ _ rfl hB]
  push_cast
  refine Finset.sum_congr rfl fun C _ => ?_
  ring

theorem finiteDimensional_minorFun {A B : Finset (Fin n)} (hB : B.card = A.card) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => minorFun n A B (x * k))) := by
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun C : Finset (Fin n) => minorFun n A C)) :=
    FiniteDimensional.span_of_finite ℂ
      (Set.finite_range (fun C : Finset (Fin n) => minorFun n A C))
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℂ (Set.range fun C : Finset (Fin n) => minorFun n A C))
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  have heq : (fun x => minorFun n A B (x * k)) = ∑ C ∈ powersetCard A.card univ,
      ((minor (k : Matrix (Fin n) (Fin n) ℝ) C B : ℝ) : ℂ) • minorFun n A C := by
    funext x
    rw [minorFun_mul hB, Finset.sum_apply]
    rfl
  change (fun x => minorFun n A B (x * k)) ∈ _
  rw [heq]
  exact Submodule.sum_mem _ fun C _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨C, rfl⟩)

/-- The value of a sign character at a sign. -/
theorem char_signUnit {A : Finset (Fin n)} (hone : ∀ l, χ l 1 = 1)
    (hsign : ∀ l : Fin n, χ l (-1) = if l ∈ A then -1 else 1) (l : Fin n) (y : ℝˣ) :
    χ l (signUnit y) = if l ∈ A then ((signReal (y : ℝ) : ℝ) : ℂ) else 1 := by
  unfold signUnit signReal
  split_ifs with h1 h2 h2 <;> simp_all

theorem minorFun_signDiagonal {A B : Finset (Fin n)} (hone : ∀ l, χ l 1 = 1)
    (hsign : ∀ l : Fin n, χ l (-1) = if l ∈ A then -1 else 1) (a : Fin n → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    minorFun n A B (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n χ (fun i => signUnit (a i)) * minorFun n A B κ := by
  rw [principalSeriesCharacter_sign]
  simp only [char_signUnit hone hsign]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  unfold minorFun
  change ((minor (Matrix.diagonal (fun i => signReal (a i : ℝ)) * (κ : Matrix (Fin n) (Fin n) ℝ))
    A B : ℝ) : ℂ) = _
  rw [minor_diagonal_mul]
  push_cast
  rfl

/-! ## Minor vectors in the principal series -/

/-- The function of the principal series extending the minor `κ ↦ det κ_{A,B}`. -/
def minorVector (n : ℕ) (e : ℕ → ℂ) (A B : Finset (Fin n)) : Langlands.GeneralLinear n ℝ → ℂ :=
  extension (shiftedExponent n e) (minorFun n A B)

theorem minorVector_mem (hχ : IsSignedPower χ e) {A B : Finset (Fin n)}
    (hsign : ∀ l : Fin n, χ l (-1) = if l ∈ A then -1 else 1) (hB : B.card = A.card) :
    minorVector n e A B ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) :=
  extension_mem_kFiniteFunctions e hχ.eq (continuous_minorFun A B) (finiteDimensional_minorFun hB)
    (minorFun_signDiagonal hχ.one hsign)

theorem minorVector_of_mem {A B : Finset (Fin n)} {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) :
    minorVector n e A B k = ((minor (k : Matrix (Fin n) (Fin n) ℝ) A B : ℝ) : ℂ) := by
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  rw [hku, minorVector, extension_unitary]
  rfl

/-- **Right translation of a minor vector by `O(n)`** (Cauchy–Binet). -/
theorem minorVector_mul (hχ : IsSignedPower χ e) {A B : Finset (Fin n)}
    (hsign : ∀ l : Fin n, χ l (-1) = if l ∈ A then -1 else 1) (hB : B.card = A.card)
    (g : Langlands.GeneralLinear n ℝ) {k₀ : Langlands.GeneralLinear n ℝ}
    (hk₀ : k₀ ∈ unitaryCompact ℝ n) :
    minorVector n e A B (g * k₀) = ∑ C ∈ powersetCard A.card univ,
      ((minor (k₀ : Matrix (Fin n) (Fin n) ℝ) C B : ℝ) : ℂ) * minorVector n e A C g := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  have hmem := (minorVector_mem hχ hsign hB).1
  rw [mul_assoc, hmem.2 a u (k * k₀), minorVector_of_mem (mul_mem hk hk₀), Units.val_mul,
    minor_mul _ _ rfl hB]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCcard : C.card = A.card := (mem_powersetCard.mp hC).2
  rw [(minorVector_mem hχ hsign hCcard).1.2 a u k, minorVector_of_mem hk]
  ring

/-! ## Minors along the chart -/

theorem chart_rows_eq_one {m : ℕ} (x : Fin m → ℝ) {i : Fin (m + 1)} (hi : i ≠ Fin.last m)
    (j : Fin (m + 1)) :
    ((chartGL x : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j := by
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.castSucc i' := ⟨i.castPred hi, by simp⟩
  rw [chartGL, JGL_val]
  simp [Jmat]

/-- **Principal minors of the orthogonal Iwasawa part of `J(x,1)`.** If
`J(x,1) = diag(a) u k`, then `det k_{A,A} = ∏_{i∈A} a_i` for `m ∉ A` and
`det k_{A,A} = (∏_{i∈A} a_i)⁻¹` for `m ∈ A`. -/
theorem minor_chart {m : ℕ} (x : Fin m → ℝ) (a : Fin (m + 1) → ℝˣ)
    (u : upperUnipotent (m + 1) ℝ) (k : Langlands.GeneralLinear (m + 1) ℝ)
    (hk : k ∈ unitaryCompact ℝ (m + 1))
    (hg : chartGL x = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * k) (A : Finset (Fin (m + 1))) :
    minor (k : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) A A =
      (∏ i ∈ A, (a i : ℝ)) ^ (if Fin.last m ∈ A then (-1 : ℤ) else 1) := by
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := (k : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((u : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set b : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.diagonal (fun i => (a i : ℝ)) * U
  set J : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((chartGL x : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  set J' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    ((chartGL (-x) : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  have hKK : K * Kᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hk
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hJ : J = b * K := by
    change ((chartGL x : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
      = _
    rw [hg, Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
  have hJ'J : J' * J = 1 := by
    have h := chartGL_mul_chartGL_neg (-x)
    rw [neg_neg] at h
    have := congrArg (fun g : Langlands.GeneralLinear (m + 1) ℝ =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) h
    simpa [Units.val_mul] using this
  have hKt : Kᵀ = J' * b := by
    calc Kᵀ = J' * J * Kᵀ := by rw [hJ'J, Matrix.one_mul]
      _ = J' * b * (K * Kᵀ) := by rw [hJ, Matrix.mul_assoc J', Matrix.mul_assoc J',
            Matrix.mul_assoc b]
      _ = J' * b := by rw [hKK, Matrix.mul_one]
  have hU : minor U A A = 1 := by
    rw [minor_of_isUpperTriangular u.2.1]
    exact Finset.prod_eq_one fun i _ => u.2.2 i
  -- the case `m ∉ A`
  have hcase : ∀ B : Finset (Fin (m + 1)), Fin.last m ∉ B → minor K B B = ∏ i ∈ B, (a i : ℝ) := by
    intro B hB
    rw [← minor_transpose, hKt, minor_mul _ _ rfl rfl]
    have hrows : ∀ i ∈ B, ∀ j, J' i j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i j :=
      fun i hi j => chart_rows_eq_one (-x) (fun h => hB (h ▸ hi)) j
    simp only [minor_of_rows_eq_one hrows]
    rw [Finset.sum_eq_single B]
    · simp only [↓reduceIte]
      rw [one_mul, minor_diagonal_mul, minor_of_isUpperTriangular u.2.1,
        Finset.prod_eq_one (fun i _ => u.2.2 i), mul_one]
    · intro C _ hC
      simp only [hC, ↓reduceIte, zero_mul]
    · intro hB'
      exact absurd (mem_powersetCard.mpr ⟨subset_univ _, rfl⟩) hB'
  by_cases hA : Fin.last m ∈ A
  · simp only [hA, ↓reduceIte]
    rw [_root_.zpow_neg_one, minor_eq_det_mul_minor_compl hKK,
      hcase Aᶜ (fun h => (Finset.mem_compl.mp h) hA)]
    have hdetJ : J.det = 1 := by
      change ((chartGL x : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det = 1
      rw [chartGL, JGL_val, det_Jmat]
      simp
    have hdet : (∏ i, (a i : ℝ)) * K.det = 1 := by
      rw [← hdetJ, hJ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_upperUnipotent u,
        mul_one]
    rw [← Finset.prod_mul_prod_compl A] at hdet
    have hA0 : (∏ i ∈ A, (a i : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (a i).ne_zero
    refine eq_inv_of_mul_eq_one_left ?_
    linear_combination hdet
  · simp only [hA, ↓reduceIte]
    rw [zpow_one]
    exact hcase A hA

/-! ## Minors of `diag(κ, 1)` -/

/-- The row set `A' = {i | castSucc i ∈ A}`. -/
def restrictSet {m : ℕ} (A : Finset (Fin (m + 1))) : Finset (Fin m) :=
  univ.filter fun i => Fin.castSucc i ∈ A

theorem mem_restrictSet {m : ℕ} {A : Finset (Fin (m + 1))} {i : Fin m} :
    i ∈ restrictSet A ↔ Fin.castSucc i ∈ A := by
  simp [restrictSet]

theorem map_restrictSet {m : ℕ} {A : Finset (Fin (m + 1))} (hA : Fin.last m ∉ A) :
    (restrictSet A).map Fin.castSuccEmb = A := by
  ext j
  induction j using Fin.lastCases with
  | last => simp [hA, Fin.castSucc_ne_last]
  | cast i => simp [mem_restrictSet]

theorem map_compl_restrictSet {m : ℕ} {A : Finset (Fin (m + 1))} (hA : Fin.last m ∈ A) :
    (restrictSet A)ᶜ.map Fin.castSuccEmb = Aᶜ := by
  ext j
  induction j using Fin.lastCases with
  | last => simp [hA, Fin.castSucc_ne_last]
  | cast i => simp [mem_restrictSet]

theorem submatrix_iota {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ) :
    (iota X).submatrix Fin.castSucc Fin.castSucc = X := by
  ext i j
  simp

theorem minor_iota {m : ℕ} {κ : Matrix (Fin m) (Fin m) ℝ} (hκ : κ * κᵀ = 1)
    (A : Finset (Fin (m + 1))) : minor (iota κ) A A = minor κ (restrictSet A) (restrictSet A) := by
  by_cases hA : Fin.last m ∈ A
  · have hιι : iota κ * (iota κ)ᵀ = 1 := by rw [iota_transpose, ← iota_mul, hκ, iota_one]
    rw [minor_eq_det_mul_minor_compl hιι, minor_eq_det_mul_minor_compl hκ, det_iota,
      ← map_compl_restrictSet hA, ← minor_submatrix_castSucc, submatrix_iota]
  · rw [← map_restrictSet hA, ← minor_submatrix_castSucc, submatrix_iota, map_restrictSet hA]

/-! ## Sign substitutions -/

/-- The principal-series character at the sign vector with a single `-1` in position `j₀`. -/
theorem principalSeriesCharacter_single {N : ℕ} (hone : ∀ l, χ l 1 = 1) {A : Finset (Fin N)}
    (hsign : ∀ l : Fin N, χ l (-1) = if l ∈ A then -1 else 1) (j₀ : Fin N) :
    principalSeriesCharacter ℝ N χ (fun i => if i = j₀ then -1 else 1) =
      if j₀ ∈ A then -1 else 1 := by
  rw [principalSeriesCharacter, Finset.prod_eq_single j₀]
  · simp [hsign]
  · intro i _ hi
    simp [hi, hone]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

/-- The product of the single-sign vector over a set. -/
theorem prod_single_sign {N : ℕ} (C : Finset (Fin N)) (j₀ : Fin N) :
    ∏ i ∈ C, (((if i = j₀ then -1 else 1 : ℝˣ)) : ℝ) = if j₀ ∈ C then -1 else 1 := by
  have h : ∀ i, (((if i = j₀ then -1 else 1 : ℝˣ)) : ℝ) = if i = j₀ then -1 else 1 := fun i => by
    split_ifs <;> simp
  simp only [h]
  exact Finset.prod_ite_eq' C j₀ (fun _ => (-1 : ℝ))

/-- **Vanishing of the off-diagonal chart integrals.** For `C ≠ A` with `|C| = |A|`,
`∫ φ_{A,C}(J(x,1)) dx = 0`: substituting a sign in a coordinate `j < m` with
`j ∈ A Δ C` multiplies the integral by `-1` on one side and by `+1` on the other. -/
theorem integral_minorVector_eq_zero (hχ : IsSignedPower χ e) {m : ℕ} {A C : Finset (Fin (m + 1))}
    (hsign : ∀ l : Fin (m + 1), χ l (-1) = if l ∈ A then -1 else 1) (hC : C.card = A.card)
    (hCA : C ≠ A) : ∫ x : Fin m → ℝ, minorVector (m + 1) e A C (chartGL x) = 0 := by
  -- a coordinate `j < m` in the symmetric difference of `A` and `C`
  obtain ⟨j, hj⟩ : ∃ j : Fin m, (Fin.castSucc j ∈ A ↔ Fin.castSucc j ∉ C) := by
    obtain ⟨i, hiA, hiC⟩ : ∃ i ∈ A, i ∉ C := by
      by_contra h
      push Not at h
      exact hCA (Finset.eq_of_subset_of_card_le (fun x hx => h x hx) (by omega)).symm
    obtain ⟨c, hcC, hcA⟩ : ∃ c ∈ C, c ∉ A := by
      by_contra h
      push Not at h
      exact hCA (Finset.eq_of_subset_of_card_le (fun x hx => h x hx) (by omega))
    by_cases hi : i = Fin.last m
    · have hc : c ≠ Fin.last m := fun h => hcA (h ▸ hi ▸ hiA)
      exact ⟨c.castPred hc, by simp [hcC, hcA]⟩
    · exact ⟨i.castPred hi, by simp [hiA, hiC]⟩
  set t : Fin (m + 1) → ℝˣ := fun l => if l = Fin.castSucc j then -1 else 1 with ht
  set s : Fin m → ℝˣ := fun l => if l = j then -1 else 1 with hs
  have hts : (fun l => Fin.lastCases 1 s l) = t := by
    funext l
    induction l using Fin.lastCases with
    | last => simp [ht, (Fin.castSucc_ne_last j).symm]
    | cast i => simp [ht, hs]
  have hD : iotaGL (Iwasawa.diagonalUnits s : Langlands.GeneralLinear m ℝ) =
      Iwasawa.diagonalUnits t := by
    rw [iotaGL_diagonalUnits, hts]
  have habsdet : |((Iwasawa.diagonalUnits s : Langlands.GeneralLinear m ℝ) :
      Matrix (Fin m) (Fin m) ℝ).det| = 1 := by
    rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Finset.abs_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [hs]
    split_ifs <;> simp
  have hdet : ((Iwasawa.diagonalUnits s : Langlands.GeneralLinear m ℝ) :
      Matrix (Fin m) (Fin m) ℝ).det ≠ 0 := fun h => by
    rw [h, abs_zero] at habsdet
    exact zero_ne_one habsdet
  have hmem := (minorVector_mem hχ hsign hC).1
  have hχt : principalSeriesCharacter ℝ (m + 1) χ t = if Fin.castSucc j ∈ A then -1 else 1 :=
    principalSeriesCharacter_single hχ.one hsign _
  -- first evaluation: the torus `diag(t)` passes through the chart
  have ha : ∀ x : Fin m → ℝ, minorVector (m + 1) e A C (chartGL x * Iwasawa.diagonalUnits t) =
      (if Fin.castSucc j ∈ A then -1 else 1) * minorVector (m + 1) e A C
        (chartGL (x ᵥ* ((Iwasawa.diagonalUnits s : Langlands.GeneralLinear m ℝ) :
          Matrix (Fin m) (Fin m) ℝ))) := by
    intro x
    rw [← hD, chartGL_mul_iotaGL, hD, ← hχt]
    have h := hmem.2 t 1 (chartGL (x ᵥ* ((Iwasawa.diagonalUnits s : Langlands.GeneralLinear m ℝ) :
      Matrix (Fin m) (Fin m) ℝ)))
    rwa [OneMemClass.coe_one, mul_one] at h
  -- second evaluation: right translation by `diag(t) ∈ O(m+1)`
  have hk₀ : (Iwasawa.diagonalUnits t : Langlands.GeneralLinear (m + 1) ℝ) ∈
      unitaryCompact ℝ (m + 1) := by
    rw [← hD]
    refine iotaGL_mem_unitaryCompact ?_
    change ((Iwasawa.diagonalUnits s : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) ∈
      Matrix.unitaryGroup (Fin m) ℝ
    rw [Matrix.mem_unitaryGroup_iff, Iwasawa.diagonalUnits_val, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [hs, Pi.star_apply, star_trivial]
    split_ifs <;> simp
  have hb : ∀ x : Fin m → ℝ, minorVector (m + 1) e A C (chartGL x * Iwasawa.diagonalUnits t) =
      (if Fin.castSucc j ∈ C then -1 else 1) * minorVector (m + 1) e A C (chartGL x) := by
    intro x
    rw [minorVector_mul hχ hsign hC _ hk₀, Finset.sum_eq_single C]
    · rw [Iwasawa.diagonalUnits_val, minor_diagonal]
      simp only [↓reduceIte]
      rw [prod_single_sign]
      split_ifs <;> simp
    · intro C' _ hC'
      rw [Iwasawa.diagonalUnits_val, minor_diagonal]
      simp [hC']
    · intro hC'
      exact absurd (mem_powersetCard.mpr ⟨subset_univ _, hC⟩) hC'
  have hab : (if Fin.castSucc j ∈ A then (-1 : ℂ) else 1) *
      ∫ x : Fin m → ℝ, minorVector (m + 1) e A C (chartGL x) =
      (if Fin.castSucc j ∈ C then (-1 : ℂ) else 1) *
      ∫ x : Fin m → ℝ, minorVector (m + 1) e A C (chartGL x) := by
    rw [← integral_const_mul, ← integral_const_mul]
    have h1 : ∫ x : Fin m → ℝ, (if Fin.castSucc j ∈ A then (-1 : ℂ) else 1) *
        minorVector (m + 1) e A C (chartGL x) =
        ∫ x : Fin m → ℝ, minorVector (m + 1) e A C (chartGL x * Iwasawa.diagonalUnits t) := by
      simp_rw [ha]
      rw [integral_const_mul, integral_const_mul,
        integral_vecMul_eq hdet (fun x => minorVector (m + 1) e A C (chartGL x)), habsdet, inv_one,
        Complex.ofReal_one, one_mul]
    rw [h1]
    simp_rw [hb]
  by_cases hjA : Fin.castSucc j ∈ A
  · have hjC : Fin.castSucc j ∉ C := hj.mp hjA
    simp only [hjA, hjC, ↓reduceIte] at hab
    linear_combination (-1 / 2 : ℂ) * hab
  · have hjC : Fin.castSucc j ∈ C := by
      by_contra h
      exact hjA (hj.mpr h)
    simp only [hjA, hjC, ↓reduceIte] at hab
    linear_combination (1 / 2 : ℂ) * hab

/-! ## The diagonal chart integral -/

/-- **The diagonal chart integral does not vanish.** Along the chart, `φ_{A,A}(J(x,1))` is the
product `∏_{l<m} r_{l+1}(x)^{d_l}` of `PartialSqIntegral`, whose exponents satisfy the tail
condition by strict dominance. -/
theorem integral_minorVector_ne_zero (hχ : IsSignedPower χ e) {m : ℕ}
    (he : IsStrictlyDominant e m) {A : Finset (Fin (m + 1))}
    (hsign : ∀ l : Fin (m + 1), χ l (-1) = if l ∈ A then -1 else 1) :
    ∫ x : Fin m → ℝ, minorVector (m + 1) e A A (chartGL x) ≠ 0 := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℤ, σ = if Fin.last m ∈ A then -1 else 1 := ⟨_, rfl⟩
  have hσ : σ = 1 ∨ σ = -1 := by
    rw [hσdef]
    split_ifs <;> simp
  have hmem := (minorVector_mem hχ hsign rfl).1
  have hpt : ∀ x : Fin m → ℝ, minorVector (m + 1) e A A (chartGL x) =
      ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^
        ((torusExponent e A σ l.succ - torusExponent e A σ (Fin.castSucc l)) / 2) := by
    intro x
    obtain ⟨a, u, k, hk, hg⟩ :=
      exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact (chartGL x)
    rw [← prod_abs_cpow_chart x a u k hk hg (torusExponent e A σ),
      ← principalSeriesCharacter_mul_prod_zpow hχ hsign hσ a, hg, hmem.2 a u k,
      minorVector_of_mem hk, minor_chart x a u k hk hg A, ← hσdef, Complex.ofReal_zpow]
  simp_rw [hpt]
  exact (integrable_and_integral_prod_ne_zero (tailCondition_torusExponent he hσdef)).2

/-! ## One step of the Jacquet integral -/

theorem shiftChar_sign {m : ℕ} {A : Finset (Fin (m + 1))}
    (hsign : ∀ l : Fin (m + 1), χ l (-1) = if l ∈ A then -1 else 1) (l : Fin m) :
    shiftChar χ l (-1) = if l ∈ restrictSet A then -1 else 1 := by
  have h := hsign (Fin.castSucc l)
  rw [Fin.val_castSucc] at h
  simp [shiftChar, h, mem_restrictSet]

/-- **The partial Jacquet integral of a principal minor vector.** With
`A' = {i < m | i ∈ A}`, `T φ_{A,A} = (∫ φ_{A,A}(J(x,1)) dx) · φ_{A',A'}`. -/
theorem jacquetStep_minorVector (hχ : IsSignedPower χ e) {m : ℕ} (he : IsStrictlyDominant e m)
    {A : Finset (Fin (m + 1))} (hsign : ∀ l : Fin (m + 1), χ l (-1) = if l ∈ A then -1 else 1) :
    jacquetStep (minorVector (m + 1) e A A) =
      (∫ x : Fin m → ℝ, minorVector (m + 1) e A A (chartGL x)) •
        minorVector m (fun l => e l - 1 / 2) (restrictSet A) (restrictSet A) := by
  have hmemK := minorVector_mem hχ hsign rfl
  have hsign' := shiftChar_sign hsign
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries (jacquetStep_mem hχ he hmemK).1
    (Submodule.smul_mem _ _ (minorVector_mem hχ.shift hsign' rfl).1) fun k hk => ?_
  have hkk : (k : Matrix (Fin m) (Fin m) ℝ) * (k : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hk
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hint : ∀ C ∈ powersetCard A.card (univ : Finset (Fin (m + 1))),
      Integrable fun x : Fin m → ℝ =>
        ((minor ((iotaGL k : Langlands.GeneralLinear (m + 1) ℝ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) C A : ℝ) : ℂ) *
          minorVector (m + 1) e A C (chartGL x) := by
    intro C hC
    have hCc : C.card = A.card := (mem_powersetCard.mp hC).2
    have h := integrable_chart hχ he (minorVector_mem hχ hsign hCc).1
      (unitaryCompact ℝ (m + 1)).one_mem
    simp only [mul_one] at h
    exact h.const_mul _
  rw [Pi.smul_apply, smul_eq_mul, minorVector_of_mem hk, jacquetStep]
  simp_rw [minorVector_mul (B := A) hχ hsign rfl _ (iotaGL_mem_unitaryCompact hk)]
  rw [integral_finsetSum _ hint, Finset.sum_eq_single A]
  · rw [integral_const_mul, iotaGL_val, minor_iota hkk, mul_comm]
  · intro C hC hCA
    rw [integral_const_mul, integral_minorVector_eq_zero hχ hsign (mem_powersetCard.mp hC).2 hCA,
      mul_zero]
  · intro hA
    exact absurd (mem_powersetCard.mpr ⟨subset_univ _, rfl⟩) hA

/-! ## Nonvanishing -/

/-- **The Jacquet integral of a principal minor vector does not vanish.** For strictly
dominant signed-power characters with `χ_l(-1) = -1` exactly for `l ∈ A`,
`Λ_n(φ_{A,A}) ≠ 0`. -/
theorem jacquet_minorVector_ne_zero : ∀ (n : ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ},
    IsSignedPower χ e → IsStrictlyDominant e (n - 1) → ∀ {A : Finset (Fin n)},
    (∀ l : Fin n, χ l (-1) = if l ∈ A then -1 else 1) → jacquet n (minorVector n e A A) ≠ 0
  | 0, χ, e, _, _, A, _ => by
      change minorVector 0 e A A 1 ≠ 0
      rw [minorVector_of_mem (unitaryCompact ℝ 0).one_mem, Finset.eq_empty_of_isEmpty A,
        minor_empty, Complex.ofReal_one]
      exact one_ne_zero
  | m + 1, χ, e, hχ, he, A, hsign => by
      have he' : IsStrictlyDominant e m := by simpa using he
      change jacquet m (jacquetStep (minorVector (m + 1) e A A)) ≠ 0
      rw [jacquetStep_minorVector hχ he' hsign, jacquet_smul]
      exact mul_ne_zero (integral_minorVector_ne_zero hχ he' hsign)
        (jacquet_minorVector_ne_zero m hχ.shift (isStrictlyDominant_shift he')
          (shiftChar_sign hsign))

end JacquetMinor

end Langlands.Archimedean
