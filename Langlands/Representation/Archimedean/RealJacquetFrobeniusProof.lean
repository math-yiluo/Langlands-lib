import Langlands.Representation.Archimedean.RealJacquetReduction
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Frobenius reciprocity for real Jacquet functionals

Proof of `Langlands.Archimedean.RealJacquetFrobeniusStatement`: a nonzero real Jacquet
functional `ℓ` with exponents `a` and signs `e` on a `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` gives the
nonzero intertwining map `B v (b k) = χ(b) ℓ(ρ(k) v)` (`b` upper triangular, `k ∈ O(n)`,
`χ(b) = ∏ⱼ sgn(b_jj)^{e_j} |b_jj|^{a_j}`) into the `O(n)`-finite functions of the principal
series of the characters `sgn^{e_j} |·|^{a_j - (n-1)/2 + j}`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealJacquetFrobenius

open Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## The characters `x ↦ sgn(x)^e |x|^t` -/

section Character

/-- `x ↦ sgn(x)^e |x|^t` on the real line, with the sign written as `x / |x|`. -/
def charFun (e : Fin 2) (t : ℂ) (x : ℝ) : ℂ :=
  (((x / |x| : ℝ)) : ℂ) ^ e.val * ((|x| : ℝ) : ℂ) ^ t

theorem charFun_mul (e : Fin 2) (t : ℂ) (x y : ℝ) :
    charFun e t (x * y) = charFun e t x * charFun e t y := by
  unfold charFun
  rw [abs_mul, mul_div_mul_comm, Complex.ofReal_mul, mul_pow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg x) (abs_nonneg y)]
  ring

theorem charFun_ne_zero (e : Fin 2) (t : ℂ) {x : ℝ} (hx : x ≠ 0) : charFun e t x ≠ 0 := by
  unfold charFun
  have h1 : (x / |x| : ℝ) ≠ 0 := div_ne_zero hx (abs_ne_zero.mpr hx)
  have h2 : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
  refine mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h1)) ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  tauto

theorem charFun_one (e : Fin 2) (t : ℂ) : charFun e t 1 = 1 := by
  simp [charFun]

theorem charFun_neg_one (e : Fin 2) (t : ℂ) : charFun e t (-1) = (-1) ^ e.val := by
  simp [charFun]

/-- `charFun e t` is smooth away from `0`. -/
theorem contDiffAt_charFun (e : Fin 2) (t : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (charFun e t) x := by
  have habs : ContDiffAt ℝ ∞ (fun y : ℝ => |y|) x := contDiffAt_abs hx
  have hsgn : ContDiffAt ℝ ∞ (fun y : ℝ => (((y / |y| : ℝ)) : ℂ) ^ e.val) x := by
    have h : ContDiffAt ℝ ∞ (fun y : ℝ => y / |y|) x :=
      contDiffAt_id.div habs (abs_ne_zero.mpr hx)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x h).pow _
  have hpow : ContDiffAt ℝ ∞ (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ t) x := by
    have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => ((|y| : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x habs
    have hslit : ((|x| : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.mpr (abs_pos.mpr hx)
    have h2 : ContDiffAt ℂ ∞ (fun z : ℂ => z ^ t) ((|x| : ℝ) : ℂ) :=
      (analyticAt_id.cpow analyticAt_const hslit).contDiffAt
    exact (h2.restrict_scalars ℝ).comp x h1
  exact hsgn.mul hpow

/-- The continuous character `x ↦ sgn(x)^e |x|^t` of `ℝ^×`. -/
def charHom (e : Fin 2) (t : ℂ) : ℝˣ →ₜ* ℂˣ where
  toFun x := Units.mk0 (charFun e t x) (charFun_ne_zero e t x.ne_zero)
  map_one' := by
    ext
    simp [charFun_one]
  map_mul' x y := by
    ext
    simp [charFun_mul e t]
  continuous_toFun := by
    rw [Units.continuous_iff]
    have hc : Continuous fun x : ℝˣ => charFun e t (x : ℝ) :=
      continuous_iff_continuousAt.mpr fun x =>
        (contDiffAt_charFun e t x.ne_zero).continuousAt.comp Units.continuous_val.continuousAt
    refine ⟨hc, ?_⟩
    convert hc.inv₀ (fun x => charFun_ne_zero e t x.ne_zero) using 1
    funext x
    simp

/-- The real character data with parity `e` and exponent `t`. -/
def charData (e : Fin 2) (t : ℂ) : RealCharacterData where
  character := charHom e t
  parity := e
  exponent := t
  character_eq _ := rfl

theorem charData_character_apply (e : Fin 2) (t : ℂ) (x : ℝˣ) :
    ((charData e t).character x : ℂ) = charFun e t x :=
  rfl

/-- The position characters of a list of real character blocks are the characters in order. -/
theorem realPositionCharacter_map_character :
    ∀ (cs : List RealCharacterData) (i : ℕ) (hi : i < cs.length) (x : ℝˣ),
      realPositionCharacter (cs.map RealBlock.character) i x = (cs[i].character x : ℂ)
  | [], _, hi, _ => by simp at hi
  | c :: cs, 0, _, x => by simp [realPositionCharacter]
  | c :: cs, i + 1, hi, x => by
      simp only [List.map_cons, realPositionCharacter, List.getElem_cons_succ]
      exact realPositionCharacter_map_character cs i (by simpa using hi) x

/-- `charFun e t x · |x|^s = charFun e (t + s) x` for `x ≠ 0`. -/
theorem charFun_mul_cpow (e : Fin 2) (t s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    charFun e t x * ((|x| : ℝ) : ℂ) ^ s = charFun e (t + s) x := by
  unfold charFun
  have h : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
  rw [Complex.cpow_add _ _ h]
  ring

end Character

/-! ## The character of the upper triangular Borel subgroup -/

section Diag

variable {n : ℕ}

theorem upper_mul_apply_self {A C : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

/-- `χ(M) = ∏ⱼ sgn(M_jj)^{e_j} |M_jj|^{a_j}`, read off the diagonal of `M`; it is a character
on the invertible upper triangular matrices. -/
def diagChar (a : Fin n → ℂ) (e : Fin n → Fin 2) (M : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  ∏ j, charFun (e j) (a j) (M j j)

theorem diagChar_mul (a : Fin n → ℂ) (e : Fin n → Fin 2) {A C : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) :
    diagChar a e (A * C) = diagChar a e A * diagChar a e C := by
  unfold diagChar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [upper_mul_apply_self hA hC, charFun_mul]

theorem diagChar_of_diag_eq_one (a : Fin n → ℂ) (e : Fin n → Fin 2)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ j, M j j = 1) : diagChar a e M = 1 := by
  simp [diagChar, hM, charFun_one]

theorem diagChar_one (a : Fin n → ℂ) (e : Fin n → Fin 2) : diagChar a e 1 = 1 :=
  diagChar_of_diag_eq_one a e fun j => Matrix.one_apply_eq j

theorem diag_ne_zero {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular) (hu : IsUnit b)
    (j : Fin n) : b j j ≠ 0 := by
  have h := (Matrix.isUnit_iff_isUnit_det b).mp hu
  rw [Matrix.det_of_isUpperTriangular hb] at h
  exact Finset.prod_ne_zero_iff.mp h.ne_zero j (Finset.mem_univ j)

/-- The entry `M ↦ M i j` as a continuous linear map. -/
def entryCLM (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem entryCLM_apply (i j : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) : entryCLM i j A = A i j :=
  rfl

theorem contDiffAt_diagChar (a : Fin n → ℂ) (e : Fin n → Fin 2) {b : Matrix (Fin n) (Fin n) ℝ}
    (hb : ∀ j, b j j ≠ 0) : ContDiffAt ℝ ∞ (diagChar a e) b := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ContDiffAt ℝ ∞ (fun M : Matrix (Fin n) (Fin n) ℝ => charFun (e j) (a j) (M j j)) b :=
    fun j _ => (contDiffAt_charFun (e j) (a j) (hb j)).comp b
      (entryCLM j j).contDiff.contDiffAt
  exact contDiffAt_prod h

/-- `charFun e t (exp x) = exp(t x)`. -/
theorem charFun_exp (e : Fin 2) (t : ℂ) (x : ℝ) :
    charFun e t (Real.exp x) = Complex.exp (x * t) := by
  unfold charFun
  rw [abs_of_pos (Real.exp_pos x), div_self (Real.exp_pos x).ne',
    RealPrincipalSeriesDuality.ofReal_exp_cpow]
  simp

end Diag

/-! ## Sign matrices -/

section Signs

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The diagonal sign matrix with `-1` exactly at the positions in `S`, in `O(n)`. -/
def signDiag (S : Finset (Fin n)) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal fun i => if i ∈ S then -1 else 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i ∈ S <;> simp [h]⟩

theorem signDiag_empty : signDiag (∅ : Finset (Fin n)) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ = 1
  simp

theorem signDiag_insert {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S) :
    signDiag (insert j S) = signReflection n j * signDiag S := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij
    simp [hj]
  · simp [hij, Finset.mem_insert]

theorem apply_signDiag (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (ℓ : V →ₗ[ℂ] ℂ) (e : Fin n → Fin 2)
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (S : Finset (Fin n)) (w : V) :
    ℓ (ρ (signDiag S) w) = (∏ j ∈ S, (-1 : ℂ) ^ (e j).val) * ℓ w := by
  induction S using Finset.induction_on generalizing w with
  | empty => simp [signDiag_empty]
  | insert j S hj ih =>
    rw [signDiag_insert hj, map_mul, Module.End.mul_apply, hsign, ih, Finset.prod_insert hj]
    ring

/-- An upper triangular orthogonal matrix is diagonal with entries `±1`. -/
theorem upper_orthogonal {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ Matrix.unitaryGroup (Fin n) ℝ)
    (hu : M.IsUpperTriangular) :
    (∀ i j, i ≠ j → M i j = 0) ∧ ∀ j, M j j = 1 ∨ M j j = -1 := by
  have hM1 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  have hinv : M⁻¹ = star M := Matrix.inv_eq_left_inv hM1
  let _ : Invertible M := invertibleOfLeftInverse M (star M) hM1
  have hup : (star M).IsUpperTriangular := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hu
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have := hup h
      simpa [Matrix.star_apply] using this
    · exact hu h
  refine ⟨hoff, fun j => ?_⟩
  have h := congrFun (congrFun hM1 j) j
  rw [Matrix.mul_apply, Fintype.sum_eq_single j] at h
  · simp only [Matrix.star_apply, star_trivial, Matrix.one_apply_eq] at h
    exact mul_self_eq_one_iff.mp h
  · intro k hk
    simp [Matrix.star_apply, hoff k j hk]

/-- `ℓ(ρ(m) w) = χ(m) ℓ(w)` for an upper triangular `m ∈ O(n)`. -/
theorem apply_upper_orthogonal (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ) (e : Fin n → Fin 2)
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (m : Matrix.unitaryGroup (Fin n) ℝ) (hu : (m : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular)
    (w : V) : ℓ (ρ m w) = diagChar a e (m : Matrix (Fin n) (Fin n) ℝ) * ℓ w := by
  classical
  obtain ⟨hoff, hpm⟩ := upper_orthogonal m.2 hu
  set S : Finset (Fin n) := Finset.univ.filter fun j => (m : Matrix (Fin n) (Fin n) ℝ) j j = -1
  have hm : m = signDiag S := by
    apply Subtype.ext
    ext i j
    change _ = Matrix.diagonal (fun i => if i ∈ S then (-1 : ℝ) else 1) i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      rcases hpm i with h | h
      · have : i ∉ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, h]
          norm_num
        simp [this, h]
      · have : i ∈ S := by simp [S, h]
        simp [this, h]
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hchar : diagChar a e (m : Matrix (Fin n) (Fin n) ℝ) = ∏ j ∈ S, (-1 : ℂ) ^ (e j).val := by
    unfold diagChar
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      fun j => (m : Matrix (Fin n) (Fin n) ℝ) j j = -1]
    have h1 : ∏ j ∈ Finset.univ.filter fun j => ¬(m : Matrix (Fin n) (Fin n) ℝ) j j = -1,
        charFun (e j) (a j) ((m : Matrix (Fin n) (Fin n) ℝ) j j) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hj' : (m : Matrix (Fin n) (Fin n) ℝ) j j = 1 :=
        (hpm j).resolve_right (Finset.mem_filter.mp hj).2
      rw [hj', charFun_one]
    rw [h1, mul_one]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.mp hj).2, charFun_neg_one]
  rw [hchar]
  conv_lhs => rw [hm]
  exact apply_signDiag ρ ℓ e hsign S w

end Signs

/-! ## The Iwasawa decomposition and the Frobenius function -/

section Iwasawa

variable {n : ℕ}

open Langlands.LinearAlgebra.TriangularUnitary

theorem exists_iwasawa (g : Langlands.GeneralLinear n ℝ) :
    ∃ b k : Matrix (Fin n) (Fin n) ℝ,
      IsTriangularUnitaryFactorization (g : Matrix (Fin n) (Fin n) ℝ) b k :=
  exists_upperTriangular_mul_unitary _ (Units.isUnit g)

/-- The upper triangular factor of a chosen Iwasawa decomposition `g = b k`. -/
def iwB (g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Classical.choose (exists_iwasawa g)

/-- The orthogonal factor of a chosen Iwasawa decomposition `g = b k`. -/
def iwK (g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Classical.choose (Classical.choose_spec (exists_iwasawa g))

theorem iw_spec (g : Langlands.GeneralLinear n ℝ) :
    IsTriangularUnitaryFactorization (g : Matrix (Fin n) (Fin n) ℝ) (iwB g) (iwK g) :=
  Classical.choose_spec (Classical.choose_spec (exists_iwasawa g))

/-- The orthogonal factor as an element of `O(n)`. -/
def iwKU (g : Langlands.GeneralLinear n ℝ) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨iwK g, (iw_spec g).2.2.1⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V) (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ)
  (e : Fin n → Fin 2)

/-- The Frobenius function `B v (b k) = χ(b) ℓ(ρ(k) v)`, through the chosen Iwasawa
decomposition. -/
def frobFun (v : V) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  diagChar a e (iwB g) * ℓ (ρ (iwKU g) v)

variable {ρ ℓ a e}

/-- `B v (b k) = χ(b) ℓ(ρ(k) v)` for every decomposition `g = b k`, `b` invertible upper
triangular and `k ∈ O(n)`. -/
theorem frobFun_eq
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    {g : Langlands.GeneralLinear n ℝ} {b k : Matrix (Fin n) (Fin n) ℝ}
    (hb : b.IsUpperTriangular) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℝ)
    (hg : (g : Matrix (Fin n) (Fin n) ℝ) = b * k) (v : V) :
    frobFun ρ ℓ a e v g = diagChar a e b * ℓ (ρ ⟨k, hk⟩ v) := by
  obtain ⟨hb', hbu', hk', hg'⟩ := iw_spec g
  have hm : iwK g * star k ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    Submonoid.mul_mem _ hk' (Unitary.star_mem hk)
  have hkk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hkk' : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk
  have hbm : iwB g * (iwK g * star k) = b := by
    rw [← mul_assoc, ← hg', hg, mul_assoc, hkk', mul_one]
  have hmu : (iwK g * star k).IsUpperTriangular := by
    let _ := hbu'.invertible
    have h : iwK g * star k = (iwB g)⁻¹ * b := by
      rw [← hbm, ← mul_assoc, Matrix.inv_mul_of_invertible, one_mul]
    rw [h]
    exact (Matrix.blockTriangular_inv_of_blockTriangular hb').mul hb
  have hρ : ρ (iwKU g) v = ρ ⟨iwK g * star k, hm⟩ (ρ ⟨k, hk⟩ v) := by
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    apply Subtype.ext
    change iwK g = iwK g * star k * k
    rw [mul_assoc, hkk, mul_one]
  unfold frobFun
  rw [hρ, apply_upper_orthogonal ρ ℓ a e hsign ⟨iwK g * star k, hm⟩ hmu, ← mul_assoc,
    ← diagChar_mul a e hb' hmu]
  change diagChar a e (iwB g * (iwK g * star k)) * _ = _
  rw [hbm]

end Iwasawa

/-! ## The principal series characters and left equivariance -/

section Equivariance

variable {n : ℕ}

/-- The exponents `a_j - (n - 1)/2 + j` of the characters of the principal series. -/
def expo (a : Fin n → ℂ) (j : Fin n) : ℂ := a j - ((n : ℂ) - 1) / 2 + ((j : ℕ) : ℂ)

/-- The real characters `sgn^{e_j} |·|^{a_j - (n-1)/2 + j}`. -/
def chars (a : Fin n → ℂ) (e : Fin n → Fin 2) (j : Fin n) : RealCharacterData :=
  charData (e j) (expo a j)

/-- The position characters of the list of the characters `chars a e`. -/
abbrev posChar (a : Fin n → ℂ) (e : Fin n → Fin 2) : ℕ → ℝˣ → ℂ :=
  realPositionCharacter ((List.ofFn (chars a e)).map RealBlock.character)

theorem posChar_apply (a : Fin n → ℂ) (e : Fin n → Fin 2) (j : Fin n) (x : ℝˣ) :
    posChar a e j x = charFun (e j) (expo a j) x := by
  rw [posChar, realPositionCharacter_map_character _ j (by simp)]
  simp [List.getElem_ofFn, chars, charData_character_apply]

/-- The character of the principal series on `diag(d)` is `χ(diag(d))`. -/
theorem principalSeriesCharacter_eq (a : Fin n → ℂ) (e : Fin n → Fin 2) (d : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (posChar a e) d =
      diagChar a e (Matrix.diagonal fun i => (d i : ℝ)) := by
  unfold principalSeriesCharacter diagChar
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [posChar_apply, Matrix.diagonal_apply_eq, Module.finrank_self, pow_one, Real.norm_eq_abs,
    charFun_mul_cpow _ _ _ (d j).ne_zero]
  congr 1
  unfold expo
  ring

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V} {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ}
  {e : Fin n → Fin 2}

/-- Left equivariance of the Frobenius function under `diag(d) u`. -/
theorem frobFun_left
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (v : V) (d : Fin n → ℝˣ) (u : Langlands.GeneralLinear.upperUnipotent n ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    frobFun ρ ℓ a e v ((Langlands.GeneralLinear.Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * g) =
      principalSeriesCharacter ℝ n (posChar a e) d * frobFun ρ ℓ a e v g := by
  obtain ⟨hb, -, hk, hg⟩ := iw_spec g
  have hD : (Matrix.diagonal fun i => (d i : ℝ)).IsUpperTriangular :=
    Matrix.blockTriangular_diagonal _
  have hu : ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular :=
    u.2.1
  have hval : (((Langlands.GeneralLinear.Iwasawa.diagonalUnits d : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * g : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
      (Matrix.diagonal (fun i => (d i : ℝ)) *
        ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * iwB g) * iwK g := by
    rw [Units.val_mul, Units.val_mul, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, hg]
    simp only [mul_assoc]
  rw [frobFun_eq hsign ((hD.mul hu).mul hb) hk hval v, diagChar_mul a e (hD.mul hu) hb,
    diagChar_mul a e hD hu, diagChar_of_diag_eq_one a e (M := ((u : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ)) (fun j => u.2.2 j), mul_one, principalSeriesCharacter_eq,
    mul_assoc]
  rfl

end Equivariance

/-! ## The Frobenius map and `O(n)`-equivariance -/

section Linear

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V) (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ)
  (e : Fin n → Fin 2)

/-- The Frobenius map `v ↦ B v`. -/
def frobLin : V →ₗ[ℂ] (Langlands.GeneralLinear n ℝ → ℂ) where
  toFun v := frobFun ρ ℓ a e v
  map_add' v w := by
    funext g
    simp [frobFun, mul_add]
  map_smul' c v := by
    funext g
    simp only [frobFun, map_smul, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
    ring

theorem frobLin_apply (v : V) : frobLin ρ ℓ a e v = frobFun ρ ℓ a e v := rfl

variable {ρ ℓ a e}

/-- `B (ρ(k) v) = R(k) (B v)` for `k ∈ O(n)`. -/
theorem frobFun_rightTranslation
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (k : unitaryCompact ℝ n) (v : V) :
    frobFun ρ ℓ a e (ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ v) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (frobFun ρ ℓ a e v) := by
  funext g
  change _ = frobFun ρ ℓ a e v (g * k)
  obtain ⟨hb, -, hk, hg⟩ := iw_spec g
  have hkk : iwK g * ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) ∈
      Matrix.unitaryGroup (Fin n) ℝ := Submonoid.mul_mem _ hk k.2
  have hval : ((g * k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      iwB g * (iwK g * ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [Units.val_mul, hg, mul_assoc]
  rw [frobFun_eq hsign hb hkk hval v]
  unfold frobFun
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

/-- The Frobenius functions are `O(n)`-finite. -/
theorem frobFun_mem_kFiniteVectors
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (v : V) (hv : FiniteVectors.IsFiniteVector ρ v) :
    frobFun ρ ℓ a e v ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) := by
  rw [mem_kFiniteVectors_iff]
  have hfin : FiniteDimensional ℂ ((FiniteVectors.orbitSpan ρ v).map (frobLin ρ ℓ a e)) := by
    have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v) := hv
    infer_instance
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
        (frobFun ρ ℓ a e v)) ≤ (FiniteVectors.orbitSpan ρ v).map (frobLin ρ ℓ a e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ v,
      FiniteVectors.action_mem_orbitSpan ρ _ v, ?_⟩
    rw [frobLin_apply, frobFun_rightTranslation hsign]
  exact Submodule.finiteDimensional_of_le hle

end Linear

/-! ## Local smooth Iwasawa coordinates -/

section Split

variable {n : ℕ}

/-- The antisymmetric part `S` of the decomposition `M = U + S` with `U` upper triangular and
`S` antisymmetric: `S i j = M i j` below the diagonal. -/
def skewPartLin : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun M := Matrix.of fun i j => if j < i then M i j else if i < j then -M j i else 0
  map_add' M N := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c M := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The antisymmetric part, as a continuous linear map. -/
def skewPart : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap skewPartLin

/-- The upper triangular part `U = M - S`. -/
def upperPart : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.id ℝ _ - skewPart

theorem skewPart_apply (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    skewPart M i j = if j < i then M i j else if i < j then -M j i else 0 :=
  rfl

theorem upperPart_add_skewPart (M : Matrix (Fin n) (Fin n) ℝ) :
    upperPart M + skewPart M = M := by
  simp [upperPart]

theorem upperPart_isUpperTriangular (M : Matrix (Fin n) (Fin n) ℝ) :
    (upperPart M).IsUpperTriangular := by
  intro i j hij
  change M i j - skewPart M i j = 0
  simp [skewPart_apply, show j < i from hij]

theorem skewPart_mem (M : Matrix (Fin n) (Fin n) ℝ) :
    skewPart M ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ) := by
  rw [skewAdjoint.mem_iff]
  ext i j
  simp only [Matrix.star_apply, star_trivial, Matrix.neg_apply, skewPart_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h
    simp
  · simp [h, not_lt.mpr h.le]

/-- An antisymmetric upper triangular matrix vanishes. -/
theorem eq_zero_of_skew_of_upper {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ)) (hu : S.IsUpperTriangular) : S = 0 := by
  rw [skewAdjoint.mem_iff] at hS
  ext i j
  have h := congrFun (congrFun hS i) j
  simp only [Matrix.star_apply, star_trivial, Matrix.neg_apply] at h
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [hu hij] at h
    simp only [Matrix.zero_apply]
    linarith
  · subst hij
    simp only [Matrix.zero_apply]
    linarith
  · exact hu hij

/-- The matrix exponential is smooth. -/
theorem contDiff_matExp :
    ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
  contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

/-- The map `M ↦ (b₀ + U(M)) exp(S(M))`. -/
def iwMap (b₀ M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (b₀ + upperPart M) * NormedSpace.exp (skewPart M)

/-- The derivative `M ↦ U(M) + b₀ S(M)` of `iwMap b₀` at `0`. -/
def iwDeriv (b₀ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  upperPart + (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) b₀).comp skewPart

theorem iwDeriv_apply (b₀ M : Matrix (Fin n) (Fin n) ℝ) :
    iwDeriv b₀ M = upperPart M + b₀ * skewPart M :=
  rfl

theorem contDiff_iwMap (b₀ : Matrix (Fin n) (Fin n) ℝ) : ContDiff ℝ ∞ (iwMap b₀) :=
  (contDiff_const.add upperPart.contDiff).mul (contDiff_matExp.comp skewPart.contDiff)

theorem hasFDerivAt_iwMap (b₀ : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt (iwMap b₀) (iwDeriv b₀) 0 := by
  have h1 : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℝ => b₀ + upperPart M) upperPart 0 :=
    upperPart.hasFDerivAt.const_add b₀
  have he : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
      (skewPart (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [map_zero]
    exact hasFDerivAt_exp_zero
  have h2 : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℝ => NormedSpace.exp (skewPart M))
      ((1 : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ).comp skewPart) 0 :=
    he.comp 0 skewPart.hasFDerivAt
  have h3 := h1.mul' h2
  refine h3.congr_fderiv ?_
  ext1 M
  simp [iwDeriv_apply, add_comm]

/-- `iwDeriv b₀` is injective for invertible upper triangular `b₀`. -/
theorem iwDeriv_injective {b₀ : Matrix (Fin n) (Fin n) ℝ} (hb : b₀.IsUpperTriangular)
    (hu : IsUnit b₀) : Function.Injective (iwDeriv b₀) := by
  refine (injective_iff_map_eq_zero (iwDeriv b₀)).mpr fun M hM => ?_
  rw [iwDeriv_apply] at hM
  let _ := hu.invertible
  have hbS : b₀ * skewPart M = -upperPart M := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hM
  have hS : skewPart M = -(b₀⁻¹ * upperPart M) := by
    calc skewPart M = b₀⁻¹ * (b₀ * skewPart M) :=
          (Matrix.inv_mul_cancel_left_of_invertible b₀ (skewPart M)).symm
      _ = _ := by rw [hbS, Matrix.mul_neg]
  have hSu : (skewPart M).IsUpperTriangular := by
    rw [hS]
    exact ((Matrix.blockTriangular_inv_of_blockTriangular hb).mul
      (upperPart_isUpperTriangular M)).neg
  have h0 := eq_zero_of_skew_of_upper (skewPart_mem M) hSu
  have hU : upperPart M = 0 := by
    rw [h0, Matrix.mul_zero, add_zero] at hM
    exact hM
  rw [← upperPart_add_skewPart M, hU, h0, add_zero]

/-- `iwDeriv b₀` as a continuous linear equivalence. -/
def iwDerivEquiv {b₀ : Matrix (Fin n) (Fin n) ℝ} (hb : b₀.IsUpperTriangular) (hu : IsUnit b₀) :
    Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (LinearEquiv.ofInjectiveEndo (iwDeriv b₀ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] _)
    (iwDeriv_injective hb hu)).toContinuousLinearEquiv

theorem iwDerivEquiv_coe {b₀ : Matrix (Fin n) (Fin n) ℝ} (hb : b₀.IsUpperTriangular)
    (hu : IsUnit b₀) :
    ((iwDerivEquiv hb hu : Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] _) :
      Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) = iwDeriv b₀ :=
  ContinuousLinearMap.ext fun _ => rfl

/-- **Local smooth Iwasawa coordinates.** Near an invertible upper triangular `b₀`, every matrix
is `(b₀ + U(Ψ y)) exp(S(Ψ y))` for a smooth `Ψ` with `Ψ b₀ = 0`. -/
theorem exists_localIwasawa {b₀ : Matrix (Fin n) (Fin n) ℝ} (hb : b₀.IsUpperTriangular)
    (hu : IsUnit b₀) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ,
      ContDiffAt ℝ ∞ Ψ b₀ ∧ Ψ b₀ = 0 ∧ ∀ᶠ y in nhds b₀, iwMap b₀ (Ψ y) = y := by
  have hΦc : ContDiffAt ℝ ∞ (iwMap b₀) 0 := (contDiff_iwMap b₀).contDiffAt
  have hΦd : HasFDerivAt (iwMap b₀)
      ((iwDerivEquiv hb hu : Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] _) :
        Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) 0 := by
    rw [iwDerivEquiv_coe]
    exact hasFDerivAt_iwMap b₀
  have h0 : iwMap b₀ 0 = b₀ := by simp [iwMap]
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hΦc.localInverse hΦd hn, ?_, ?_, ?_⟩
  · have key := hΦc.to_localInverse hΦd hn
    rw [h0] at key
    exact key
  · have key := hΦc.localInverse_apply_image hΦd hn
    rw [h0] at key
    exact key
  · have key := (hΦc.hasStrictFDerivAt' hΦd hn).eventually_right_inverse
    rw [h0] at key
    exact key

end Split

/-! ## Smoothness of the Frobenius functions -/

section Smooth

variable {n : ℕ}

/-- A complex polynomial in the entries of a real matrix. -/
def polyEval (P : MvPolynomial (Fin n × Fin n) ℂ) (m : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  MvPolynomial.eval (fun ij => (m ij.1 ij.2 : ℂ)) P

theorem contDiff_polyEval (P : MvPolynomial (Fin n × Fin n) ℂ) :
    ContDiff ℝ ∞ (polyEval P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : polyEval (n := n) (MvPolynomial.C c) = fun _ => c := by
      funext m
      simp [polyEval]
    rw [h]
    exact contDiff_const
  | add p q hp hq =>
    have h : polyEval (p + q) = fun m => polyEval p m + polyEval q m := by
      funext m
      simp [polyEval]
    rw [h]
    exact hp.add hq
  | mul_X p ij hp =>
    have h : polyEval (p * MvPolynomial.X ij) =
        fun m => polyEval p m * ((m ij.1 ij.2 : ℝ) : ℂ) := by
      funext m
      simp [polyEval]
    rw [h]
    exact hp.mul (Complex.ofRealCLM.contDiff.comp (entryCLM ij.1 ij.2).contDiff)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V} {ℓ : V →ₗ[ℂ] ℂ}

/-- The matrix coefficients `k ↦ ℓ(ρ(k) v)` of an `O(n)`-finite continuous representation are
polynomial in the entries of `k`. -/
theorem exists_polyEval (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ' : V →ₗ[ℂ] ℂ),
      Continuous fun k : Matrix.unitaryGroup (Fin n) ℝ => ℓ' (ρ k v))
    (v : V) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
      ℓ (ρ k v) = polyEval P (k : Matrix (Fin n) (Fin n) ℝ) := by
  let C : V →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) := LinearMap.pi fun x => ℓ ∘ₗ ρ x
  have hfd : FiniteDimensional ℂ ((FiniteVectors.orbitSpan ρ v).map C) := by
    have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v) := hfin v
    infer_instance
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x : Matrix.unitaryGroup (Fin n) ℝ => ℓ (ρ (x * k) v)) ≤
        (FiniteVectors.orbitSpan ρ v).map C := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨ρ k v, FiniteVectors.action_mem_orbitSpan ρ k v, ?_⟩
    funext x
    simp [C, map_mul]
  exact OrthogonalFinitePolynomial.exists_mvPolynomial_of_finiteDimensional_span (hcont v ℓ)
    (Submodule.finiteDimensional_of_le hle)

variable {a : Fin n → ℂ} {e : Fin n → Fin 2}

/-- The extension of `B v` to the matrices is smooth at every invertible matrix: near
`y₀ = b₀ k₀` it is `y ↦ χ(b₀ + U(Ψ(y k₀ᵀ))) P(exp(S(Ψ(y k₀ᵀ))) k₀)`. -/
theorem contDiffAt_unitsExtension_frobFun
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    {P : MvPolynomial (Fin n × Fin n) ℂ} {v : V}
    (hP : ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
      ℓ (ρ k v) = polyEval P (k : Matrix (Fin n) (Fin n) ℝ))
    {y₀ : Matrix (Fin n) (Fin n) ℝ} (hy₀ : IsUnit y₀) :
    ContDiffAt ℝ ∞ (unitsExtension (frobFun ρ ℓ a e v)) y₀ := by
  obtain ⟨hb, hbu, hk, hg⟩ := iw_spec hy₀.unit
  set b₀ := iwB hy₀.unit
  set k₀ := iwK hy₀.unit
  have hkk : k₀ * star k₀ = 1 := Matrix.mem_unitaryGroup_iff.mp hk
  have hkk' : star k₀ * k₀ = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hy : y₀ = b₀ * k₀ := hy₀.unit_spec.symm.trans hg
  have hyb : y₀ * star k₀ = b₀ := by rw [hy, mul_assoc, hkk, mul_one]
  obtain ⟨Ψ, hΨc, hΨ0, hΨe⟩ := exists_localIwasawa hb hbu
  have hT : ContDiffAt ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ => Ψ (y * star k₀)) y₀ := by
    have h1 : ContDiffAt ℝ ∞ Ψ (y₀ * star k₀) := by
      rw [hyb]
      exact hΨc
    exact h1.comp y₀ (contDiffAt_id.mul contDiffAt_const)
  have hD : ContDiffAt ℝ ∞
      (fun y : Matrix (Fin n) (Fin n) ℝ => diagChar a e (b₀ + upperPart (Ψ (y * star k₀)))) y₀ := by
    have h1 : ContDiffAt ℝ ∞ (diagChar a e) (b₀ + upperPart (Ψ (y₀ * star k₀))) := by
      rw [hyb, hΨ0, map_zero, add_zero]
      exact contDiffAt_diagChar a e (diag_ne_zero hb hbu)
    have h2 : ContDiffAt ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ =>
        b₀ + upperPart (Ψ (y * star k₀))) y₀ :=
      contDiffAt_const.add (upperPart.contDiff.contDiffAt.comp y₀ hT)
    have h3 := h1.comp y₀ h2
    exact h3
  have hQ : ContDiffAt ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℝ =>
      polyEval P (NormedSpace.exp (skewPart (Ψ (y * star k₀))) * k₀)) y₀ :=
    (contDiff_polyEval P).contDiffAt.comp y₀
      ((contDiff_matExp.contDiffAt.comp y₀ (skewPart.contDiff.contDiffAt.comp y₀ hT)).mul
        contDiffAt_const)
  refine (hD.mul hQ).congr_of_eventuallyEq ?_
  have htend : Filter.Tendsto (fun y : Matrix (Fin n) (Fin n) ℝ => y * star k₀) (nhds y₀)
      (nhds b₀) := by
    have hc : Continuous fun y : Matrix (Fin n) (Fin n) ℝ => y * star k₀ :=
      continuous_id.mul continuous_const
    exact hc.tendsto' y₀ b₀ hyb
  filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds hy₀, htend.eventually hΨe] with y hyu hyΨ
  have hyu' : IsUnit y := hyu
  have hSk : NormedSpace.exp (skewPart (Ψ (y * star k₀))) * k₀ ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    Submonoid.mul_mem _
      (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewPart_mem (Ψ (y * star k₀)))) hk
  have hbup : (b₀ + upperPart (Ψ (y * star k₀))).IsUpperTriangular :=
    hb.add (upperPart_isUpperTriangular _)
  have hval : ((hyu'.unit : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (b₀ + upperPart (Ψ (y * star k₀))) *
        (NormedSpace.exp (skewPart (Ψ (y * star k₀))) * k₀) := by
    rw [hyu'.unit_spec, ← mul_assoc]
    change y = iwMap b₀ (Ψ (y * star k₀)) * k₀
    rw [hyΨ, mul_assoc, hkk', mul_one]
  have hext : unitsExtension (frobFun ρ ℓ a e v) y = frobFun ρ ℓ a e v hyu'.unit := by
    rw [← unitsExtension_val (frobFun ρ ℓ a e v) hyu'.unit, hyu'.unit_spec]
  rw [hext, frobFun_eq hsign hbup hSk hval v, hP]

/-- The Frobenius functions are smooth. -/
theorem contMDiff_frobFun
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ' : V →ₗ[ℂ] ℂ),
      Continuous fun k : Matrix.unitaryGroup (Fin n) ℝ => ℓ' (ρ k v))
    (v : V) : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (frobFun ρ ℓ a e v) := by
  obtain ⟨P, hP⟩ := exists_polyEval (ℓ := ℓ) hfin hcont v
  exact contMDiff_of_contDiffOn (ψ := unitsExtension (frobFun ρ ℓ a e v))
    (fun y hy => (contDiffAt_unitsExtension_frobFun hsign hP hy).contDiffWithinAt)
    fun g => (unitsExtension_val _ g).symm

end Smooth

/-! ## The right derivatives -/

section RightDerivative

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {ℓ : V →ₗ[ℂ] ℂ}
  {a : Fin n → ℂ} {e : Fin n → Fin 2}

/-- `M ↦ ℓ(π(1 ⊗ M) w)` as a real linear map. -/
def actFun (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (ℓ : V →ₗ[ℂ] ℂ)
    (w : V) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℂ where
  toFun M := ℓ (π (1 ⊗ₜ M) w)
  map_add' M M' := by
    rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply, map_add]
  map_smul' r M := by
    have h : (1 : ℂ) ⊗ₜ[ℝ] (r • M) = (r : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] M) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Complex.real_smul, smul_eq_mul]
    rw [h, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
      Complex.real_smul]

theorem actFun_apply (w : V) (M : Matrix (Fin n) (Fin n) ℝ) :
    actFun π ℓ w M = ℓ (π (1 ⊗ₜ M) w) :=
  rfl

/-- `ℓ(π(1 ⊗ U) w) = (∑ⱼ aⱼ Uⱼⱼ) ℓ(w)` for an upper triangular `U`: the strictly upper part is
killed by `ℓ` and `E_jj` acts on `ℓ` by `a_j`. -/
theorem jacquet_upper (hℓ : IsRealJacquetFunctional n ρ π ℓ a e)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) (w : V) :
    ℓ (π (1 ⊗ₜ U) w) = (∑ j, a j * (U j j : ℂ)) * ℓ w := by
  set N : Matrix (Fin n) (Fin n) ℝ := U - Matrix.diagonal fun i => U i i with hN
  have hNs : ∀ i j : Fin n, (j : ℕ) ≤ i → N i j = 0 := by
    intro i j hij
    rcases Nat.lt_or_eq_of_le hij with h | h
    · have h' : j < i := h
      rw [hN, Matrix.sub_apply, hU h', Matrix.diagonal_apply_ne _ (ne_of_gt h'), sub_zero]
    · have h' : j = i := Fin.ext h
      subst h'
      simp [hN]
  have hdec : U = N + ∑ j, U j j • Matrix.single j j (1 : ℝ) := by
    have h1 : ∑ j, U j j • Matrix.single j j (1 : ℝ) = Matrix.diagonal fun i => U i i := by
      rw [← Matrix.sum_single_eq_diagonal]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h1, hN, sub_add_cancel]
  calc ℓ (π (1 ⊗ₜ U) w) = actFun π ℓ w U := rfl
    _ = actFun π ℓ w (N + ∑ j, U j j • Matrix.single j j (1 : ℝ)) := congrArg _ hdec
    _ = ∑ j, U j j • (a j * ℓ w) := by
      rw [map_add, map_sum, actFun_apply w N, hℓ.1 N hNs w, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, actFun_apply, (hℓ.2 j w).1]
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.real_smul]
      ring

/-- `χ(exp(diag x)) = exp(∑ⱼ xⱼ aⱼ)`. -/
theorem diagChar_exp_diagonal (a : Fin n → ℂ) (e : Fin n → Fin 2) (x : Fin n → ℝ) :
    diagChar a e (NormedSpace.exp (Matrix.diagonal x)) = Complex.exp (∑ j, (x j : ℂ) * a j) := by
  rw [← matrixExpUnit_val n (Matrix.diagonal x), RealPrincipalSeriesDuality.matrixExpUnit_diagonal,
    Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Complex.exp_sum]
  unfold diagChar
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_apply_eq, Units.val_mk0, charFun_exp]

/-- `B(π(1 ⊗ X) v) = R(X)(B v)`: at `g = b k`, both sides equal
`χ(b) (s ℓ(ρ(k) v) + ℓ(π(1 ⊗ Z) ρ(k) v))` where `k X kᵀ = U + Z` (`U` upper triangular, `Z`
antisymmetric) and `s = ∑ⱼ aⱼ Uⱼⱼ`; the right side is computed along the curve
`b exp(t diag U) (1 + t N) exp(t Z) k` through `g` with velocity `g X`. -/
theorem frobFun_rightDerivative (hgk : IsRealGKModule n ρ π)
    (hℓ : IsRealJacquetFunctional n ρ π ℓ a e) (X : Matrix (Fin n) (Fin n) ℝ) (v : V)
    (g : Langlands.GeneralLinear n ℝ) :
    frobFun ρ ℓ a e (π (1 ⊗ₜ X) v) g =
      rightDerivative (matrixModel ℝ n) X (frobFun ρ ℓ a e v) g := by
  have hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v :=
    fun j v => (hℓ.2 j v).2
  have hF := contMDiff_frobFun (a := a) hsign hgk.1 hgk.2.1 v
  rw [rightDerivative_eq_fderiv hF]
  obtain ⟨hb, hbu, hk, hg⟩ := iw_spec g
  set b := iwB g with hbdef
  set k := iwK g with hkdef
  set kU : Matrix.unitaryGroup (Fin n) ℝ := ⟨k, hk⟩ with hkU
  set w := ρ kU v with hw
  have hkk' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hkI : IsUnit k := by
    let _ := invertibleOfLeftInverse k (star k) hkk'
    exact isUnit_of_invertible k
  set Y := k * X * star k with hY
  set U := upperPart Y with hU
  set Z := skewPart Y with hZ
  set Δ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i => U i i with hΔ
  set N := U - Δ with hN
  have hUu : U.IsUpperTriangular := upperPart_isUpperTriangular Y
  have hNu : N.IsUpperTriangular := hUu.sub (Matrix.blockTriangular_diagonal _)
  have hNd : ∀ i, N i i = 0 := fun i => by simp [hN, hΔ]
  have hZs : Z ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℝ) := skewPart_mem Y
  set s : ℂ := ∑ j, a j * (U j j : ℂ) with hs
  -- the left side
  have hL : frobFun ρ ℓ a e (π (1 ⊗ₜ X) v) g =
      diagChar a e b * (s * ℓ w + ℓ (π (1 ⊗ₜ Z) w)) := by
    have hρ : ρ kU (π (1 ⊗ₜ X) v) = π (1 ⊗ₜ Y) w := hgk.2.2.2 kU X v
    have hYUZ : (1 : ℂ) ⊗ₜ[ℝ] Y = (1 : ℂ) ⊗ₜ[ℝ] U + (1 : ℂ) ⊗ₜ[ℝ] Z := by
      rw [← TensorProduct.tmul_add]
      exact congrArg _ (upperPart_add_skewPart Y).symm
    rw [frobFun_eq hsign hb hk hg, hρ, hYUZ, map_add, LinearMap.add_apply, map_add,
      jacquet_upper hℓ hUu w]
  -- the curve
  have hbk : (g : Matrix (Fin n) (Fin n) ℝ) * X = b * (Δ + N + Z) * k := by
    have h1 : Δ + N + Z = Y := by
      rw [hN, add_sub_cancel]
      exact upperPart_add_skewPart Y
    rw [h1, hY, hg]
    simp only [mul_assoc, hkk', mul_one]
  set Γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t =>
    b * NormedSpace.exp (t • Δ) * (1 + t • N) * (NormedSpace.exp (t • Z) * k) with hΓ
  have hΓd : HasDerivAt Γ ((g : Matrix (Fin n) (Fin n) ℝ) * X) 0 := by
    have h1 := (RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero Δ).const_mul b
    have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + t • N) N 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add 1
    have h3 := (RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero Z).mul_const k
    have h4 := (h1.mul h2).mul h3
    refine h4.congr_deriv ?_
    rw [hbk]
    simp only [Pi.mul_apply, zero_smul, add_zero, NormedSpace.exp_zero, mul_one, one_mul]
    noncomm_ring
  have hΓ0 : Γ 0 = (g : Matrix (Fin n) (Fin n) ℝ) := by
    simp only [hΓ, zero_smul, NormedSpace.exp_zero, add_zero, mul_one, one_mul]
    exact hg.symm
  have hΓu : ∀ t : ℝ, IsUnit (Γ t) := fun t =>
    ((hbu.mul (matrixExpUnit n (t • Δ)).isUnit).mul
      ((RealPrincipalSeriesDuality.unipotentLine N hNu hNd t :
        Langlands.GeneralLinear.upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ).isUnit).mul
      ((matrixExpUnit n (t • Z)).isUnit.mul hkI)
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℝ := fun t =>
    ⟨NormedSpace.exp (t • Z),
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hZs)⟩
  have hsd : ∀ t : ℝ, t • Δ = Matrix.diagonal fun i => t * U i i := by
    intro t
    rw [hΔ, ← Matrix.diagonal_smul]
    rfl
  have hval : ∀ t : ℝ, unitsExtension (frobFun ρ ℓ a e v) (Γ t) =
      diagChar a e b * (Complex.exp ((t : ℂ) * s) * ℓ (ρ (γ t) w)) := by
    intro t
    have hup1 : (NormedSpace.exp (t • Δ)).IsUpperTriangular := by
      rw [hsd t, Matrix.exp_diagonal]
      exact Matrix.blockTriangular_diagonal _
    have hup2 : (1 + t • N).IsUpperTriangular :=
      RealPrincipalSeriesDuality.isUpperTriangular_one_add_smul hNu t
    have hmem : NormedSpace.exp (t • Z) * k ∈ Matrix.unitaryGroup (Fin n) ℝ :=
      Submonoid.mul_mem _ (γ t).2 hk
    have hext : unitsExtension (frobFun ρ ℓ a e v) (Γ t) = frobFun ρ ℓ a e v (hΓu t).unit := by
      rw [← unitsExtension_val (frobFun ρ ℓ a e v) (hΓu t).unit, (hΓu t).unit_spec]
    have hdiag : diagChar a e (NormedSpace.exp (t • Δ)) = Complex.exp ((t : ℂ) * s) := by
      rw [hsd t, diagChar_exp_diagonal, hs, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    have hρk : ρ ⟨NormedSpace.exp (t • Z) * k, hmem⟩ v = ρ (γ t) w := by
      rw [hw, ← Module.End.mul_apply, ← map_mul]
      rfl
    rw [hext, frobFun_eq hsign ((hb.mul hup1).mul hup2) hmem (hΓu t).unit_spec v,
      diagChar_mul a e (hb.mul hup1) hup2, diagChar_mul a e hb hup1,
      diagChar_of_diag_eq_one a e (M := 1 + t • N) (fun j => by simp [hNd]), mul_one, hdiag,
      hρk, mul_assoc]
  -- the derivative along the curve
  have hγ0 : γ 0 = 1 := by
    apply Subtype.ext
    simp [γ]
  have hγd : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ) i j) (Z i j) 0 :=
    fun i j => RealPrincipalSeriesDuality.hasDerivAt_entry
      (RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero Z) i j
  have hℓd := hgk.2.2.1 γ Z hγ0 hγd w ℓ
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * s)) s 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const s).cexp
    simpa using this
  have hd2 : HasDerivAt
      (fun t : ℝ => diagChar a e b * (Complex.exp ((t : ℂ) * s) * ℓ (ρ (γ t) w)))
      (diagChar a e b * (s * ℓ w + ℓ (π (1 ⊗ₜ Z) w))) 0 := by
    refine ((hexp.mul hℓd).const_mul (diagChar a e b)).congr_deriv ?_
    rw [hγ0, map_one, Module.End.one_apply]
    simp
  have hd1 : HasDerivAt (fun t => unitsExtension (frobFun ρ ℓ a e v) (Γ t))
      (fderiv ℝ (unitsExtension (frobFun ρ ℓ a e v)) (g : Matrix (Fin n) (Fin n) ℝ)
        ((g : Matrix (Fin n) (Fin n) ℝ) * X)) 0 := by
    have hdiff : HasFDerivAt (unitsExtension (frobFun ρ ℓ a e v))
        (fderiv ℝ (unitsExtension (frobFun ρ ℓ a e v)) (g : Matrix (Fin n) (Fin n) ℝ))
        (Γ 0) := by
      rw [hΓ0]
      exact (differentiableAt_unitsExtension hF (Units.isUnit g)).hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hΓd
  have hfun : (fun t => unitsExtension (frobFun ρ ℓ a e v) (Γ t)) =
      fun t : ℝ => diagChar a e b * (Complex.exp ((t : ℂ) * s) * ℓ (ρ (γ t) w)) :=
    funext hval
  rw [hfun] at hd1
  rw [hL, hd1.unique hd2]

end RightDerivative

/-! ## The Frobenius map -/

section Assembly

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Frobenius reciprocity for real Jacquet functionals.** -/
theorem realJacquetFrobenius : RealJacquetFrobeniusStatement.{uV} := by
  intro n V _ _ ρ π hgk ℓ a e hℓ0 hℓ
  have hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v :=
    fun j v => (hℓ.2 j v).2
  have hmem : ∀ v : V, frobLin ρ ℓ a e v ∈ kFiniteFunctions
      (realStandardModule n ((List.ofFn (chars a e)).map RealBlock.character))
      (unitaryCompact ℝ n) := by
    intro v
    refine Submodule.mem_inf.mpr ⟨⟨(mem_principalSeries_iff ℝ n _ _).mpr
      ⟨contMDiff_frobFun hsign hgk.1 hgk.2.1 v, frobFun_left hsign v⟩, ?_⟩,
      frobFun_mem_kFiniteVectors hsign v (hgk.1 v)⟩
    intro p d hd
    rw [RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
    exact absurd hd (by simp)
  refine ⟨chars a e, fun j => rfl, fun j => ?_, (frobLin ρ ℓ a e).codRestrict _ hmem, ?_, ?_, ?_⟩
  · change expo a j + ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) = a j
    unfold expo
    ring
  · intro hB
    apply hℓ0
    refine LinearMap.ext fun v => ?_
    have h := congrFun (congrArg Subtype.val (LinearMap.congr_fun hB v)) 1
    have h0 : frobFun ρ ℓ a e v 1 = 0 := h
    have h1 : frobFun ρ ℓ a e v 1 = ℓ v := by
      rw [frobFun_eq (b := 1) (k := 1) hsign Matrix.blockTriangular_one (one_mem _) (by simp) v,
        diagChar_one, one_mul]
      change ℓ (ρ 1 v) = ℓ v
      rw [map_one, Module.End.one_apply]
    rw [← h1, h0, LinearMap.zero_apply]
  · intro k v
    exact frobFun_rightTranslation hsign k v
  · intro X v
    funext g
    exact frobFun_rightDerivative hgk hℓ X v g

end Assembly

end RealJacquetFrobenius

end Langlands.Archimedean
