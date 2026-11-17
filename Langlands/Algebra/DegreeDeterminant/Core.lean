import Langlands.Algebra.DegreeDeterminant.LineInterpolation
import Langlands.Algebra.DegreeDeterminant.MultiplicativeRoots
import Langlands.Algebra.DegreeDeterminant.PadicComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Reverse

/-! # The degree of an endomorphism is a determinant: the algebraic part

Let `R` be a ring with a ring homomorphism `ρ` to `2g × 2g` matrices over `ℚ_[p]` and a
function `δ : R → ℚ`. Suppose that `δ` is polynomial of degree at most `2g` along every line
`n ↦ n • φ + ψ`, that `δ` is multiplicative on a class of elements called isogenies, that
`|δ β|_p = |det ρ β|_p` for isogenies and `det ρ β = 0` for the other elements. Then
`δ α = det ρ α` for every `α`. This is the algebraic part of Milne's proof of Proposition 12.9
of *Abelian Varieties*.
-/

noncomputable section

open Polynomial

namespace Langlands.Algebra.DegreeDeterminant

section Coeffs

variable {S : Type*} [Semiring S] {n : ℕ}

/-- The polynomial with coefficient vector `x`. -/
def ofCoeffs (x : Fin n → S) : S[X] := ∑ i : Fin n, monomial (i : ℕ) (x i)

theorem coeff_ofCoeffs (x : Fin n → S) (m : ℕ) :
    (ofCoeffs x).coeff m = if h : m < n then x ⟨m, h⟩ else 0 := by
  classical
  rw [ofCoeffs, finsetSum_coeff]
  simp_rw [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      exact ite_eq_right_iff.mpr fun hbm => absurd (Fin.ext hbm) hb
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    exact ite_eq_right_iff.mpr fun him => absurd (him ▸ i.isLt) h

theorem coeff_ofCoeffs_fin (x : Fin n → S) (k : Fin n) : (ofCoeffs x).coeff k = x k := by
  rw [coeff_ofCoeffs]
  simp [k.isLt]

theorem ofCoeffs_coeff (F : S[X]) (hF : F.natDegree < n) :
    ofCoeffs (fun i : Fin n => F.coeff i) = F := by
  ext m
  rw [coeff_ofCoeffs]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem natDegree_ofCoeffs_lt (x : Fin n → S) (hn : 0 < n) : (ofCoeffs x).natDegree < n := by
  have : (ofCoeffs x).natDegree ≤ n - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_ofCoeffs]
    split_ifs with h
    · omega
    · rfl
  omega

theorem map_ofCoeffs {T : Type*} [Semiring T] (φ : S →+* T) (x : Fin n → S) :
    (ofCoeffs x).map φ = ofCoeffs (fun i => φ (x i)) := by
  simp [ofCoeffs, Polynomial.map_sum]

theorem ofCoeffs_update (x : Fin n → S) (i : Fin n) (m : S) :
    ofCoeffs (Function.update x i (x i + m)) = ofCoeffs x + monomial (i : ℕ) m := by
  ext k
  rw [coeff_add, coeff_ofCoeffs, coeff_ofCoeffs, coeff_monomial]
  split_ifs with h1 h2 h2
  · subst h2
    simp
  · rw [Function.update_of_ne, add_zero]
    intro hk
    exact h2 (by rw [← hk])
  · exact absurd (h2 ▸ i.isLt) h1
  · simp

end Coeffs

section Data

variable {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {g : ℕ}

/-- The hypotheses of the algebraic part of Milne's proof of Proposition 12.9. -/
structure DegreeData (ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]) (δ : R → ℚ)
    (iso : R → Prop) : Prop where
  line : ∀ φ ψ : R, ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
    ∀ n : ℕ, δ (n • φ + ψ) = P.eval (n : ℚ)
  mul : ∀ β γ : R, iso β → iso γ → δ (β * γ) = δ β * δ γ
  norm : ∀ β : R, iso β → ‖(δ β : ℚ_[p])‖ = ‖(ρ β).det‖
  zero : ∀ β : R, ¬ iso β → (ρ β).det = 0

variable {ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]} {δ : R → ℚ} {iso : R → Prop}

theorem DegreeData.iso_of_det_ne_zero (hD : DegreeData ρ δ iso) {β : R}
    (h : (ρ β).det ≠ 0) : iso β := by
  by_contra hβ
  exact h (hD.zero β hβ)

/-- `ρ` commutes with evaluation of polynomials with natural-number coefficients. -/
theorem ρ_aeval (ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]) (α : R) (G : ℕ[X]) :
    ρ (aeval α G) = aeval (ρ α) (G.map (algebraMap ℕ ℚ_[p])) := by
  rw [aeval_map_algebraMap]
  exact (Polynomial.aeval_algHom_apply (RingHom.toNatAlgHom ρ) α G).symm

/-- The values of `δ` on `F(α)`, for `F` with natural coefficients of degree less than `n`,
are given by a rational polynomial in the coefficients. -/
theorem DegreeData.exists_mvPolynomial (hD : DegreeData ρ δ iso) (α : R) (n : ℕ) :
    ∃ M : MvPolynomial (Fin n) ℚ, ∀ x : Fin n → ℕ,
      δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M := by
  apply exists_mvPolynomial_of_line (2 * g) n (fun x => δ (aeval α (ofCoeffs x)))
  intro i x
  obtain ⟨P, hP, hPe⟩ := hD.line (α ^ (i : ℕ)) (aeval α (ofCoeffs x))
  refine ⟨P, hP, fun m => ?_⟩
  rw [← hPe m]
  congr 1
  rw [ofCoeffs_update, map_add, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul, add_comm]

end Data

section CoeffEval

variable {n : ℕ} (M : MvPolynomial (Fin n) ℚ)

/-- The polynomial function of the first `n` coefficients defined by `M`. -/
def coeffEval {S : Type*} [CommRing S] [Algebra ℚ S] (F : S[X]) : S :=
  MvPolynomial.aeval (fun k : Fin n => F.coeff k) M

theorem coeffEval_map {S T : Type*} [CommRing S] [Algebra ℚ S] [CommRing T] [Algebra ℚ T]
    (φ : S →ₐ[ℚ] T) (F : S[X]) :
    coeffEval M (F.map (φ : S →+* T)) = φ (coeffEval M F) := by
  rw [coeffEval, coeffEval, MvPolynomial.comp_aeval_apply]
  simp [coeff_map]

theorem algebraMap_eval {S : Type*} [CommRing S] [Algebra ℚ S] {σ : Type*} (v : σ → ℚ)
    (Ψ : MvPolynomial σ ℚ) :
    algebraMap ℚ S (MvPolynomial.eval v Ψ) =
      MvPolynomial.aeval (fun i => algebraMap ℚ S (v i)) Ψ := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl

variable {R : Type*} [Ring R] (δ : R → ℚ) (α : R)

/-- On polynomials with natural-number coefficients, `coeffEval M` computes `δ`. -/
theorem coeffEval_natCast
    (hM : ∀ x : Fin n → ℕ, δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M)
    {S : Type*} [CommRing S] [Algebra ℚ S] (G : ℕ[X]) (hG : G.natDegree < n) :
    coeffEval M (G.map (algebraMap ℕ S)) = algebraMap ℚ S (δ (aeval α G)) := by
  have h := hM (fun i => G.coeff i)
  rw [ofCoeffs_coeff G hG] at h
  rw [h, algebraMap_eval, coeffEval]
  refine congrArg (fun v => MvPolynomial.aeval v M) (funext fun k => ?_)
  simp

end CoeffEval

section Transfer

/-- A polynomial identity over `ℚ` that holds at the natural-number points where a nonzero
polynomial `Z` over a field of characteristic zero does not vanish holds identically. -/
theorem eq_of_eval_natCast_of_ne_zero {σ K : Type*} [Field K] [CharZero K]
    (Ψ₁ Ψ₂ : MvPolynomial σ ℚ) (Z : MvPolynomial σ K) (hZ : Z ≠ 0)
    (h : ∀ w : σ → ℕ, MvPolynomial.eval (fun s => (w s : K)) Z ≠ 0 →
      MvPolynomial.eval (fun s => (w s : ℚ)) Ψ₁ = MvPolynomial.eval (fun s => (w s : ℚ)) Ψ₂) :
    Ψ₁ = Ψ₂ := by
  apply MvPolynomial.map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective
  have key : ∀ (w : σ → ℕ) (Ψ : MvPolynomial σ ℚ),
      MvPolynomial.eval (fun s => (w s : K)) (MvPolynomial.map (algebraMap ℚ K) Ψ) =
        algebraMap ℚ K (MvPolynomial.eval (fun s => (w s : ℚ)) Ψ) := by
    intro w Ψ
    rw [algebraMap_eval, MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
    funext s
    simp
  have hprod : (MvPolynomial.map (algebraMap ℚ K) Ψ₁ - MvPolynomial.map (algebraMap ℚ K) Ψ₂) *
      Z = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → K))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro x hx
    choose w hw using fun s => hx s (Set.mem_univ s)
    have hx' : x = fun s => (w s : K) := funext fun s => (hw s).symm
    subst hx'
    rw [map_zero, map_mul, map_sub, key, key]
    by_cases hz : MvPolynomial.eval (fun s => (w s : K)) Z = 0
    · rw [hz, mul_zero]
    · rw [h w hz, sub_self, zero_mul]
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hZ

end Transfer

section Edet

variable {p : ℕ} [Fact p.Prime] {g : ℕ} (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p])

/-- The determinant of `F(A)` as a function of the coefficient vector of `F`. -/
def edet {T : Type*} [CommRing T] [Algebra ℚ_[p] T] {N : ℕ} (y : Fin N → T) : T :=
  (∑ k : Fin N, y k • (A ^ (k : ℕ)).map (algebraMap ℚ_[p] T)).det

theorem edet_eq {T : Type*} [CommRing T] [Algebra ℚ_[p] T] {N : ℕ} (y : Fin N → T) :
    edet A y = (aeval (A.map (algebraMap ℚ_[p] T)) (ofCoeffs y)).det := by
  rw [edet, ofCoeffs, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [aeval_monomial, Matrix.map_pow, Algebra.smul_def]

theorem map_edet {T T' : Type*} [CommRing T] [Algebra ℚ_[p] T] [CommRing T']
    [Algebra ℚ_[p] T'] (φ : T →ₐ[ℚ_[p]] T') {N : ℕ} (y : Fin N → T) :
    φ (edet A y) = edet A (fun k => φ (y k)) := by
  rw [edet, edet, AlgHom.map_det, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [AlgHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_map]
  congr 1
  ext i j
  simp

end Edet

section Main

/-- A rational polynomial that is multiplicative on positive integers is a monomial there. -/
theorem eval_natCast_eq_pow_of_mul (P : ℚ[X]) (hP : P ≠ 0)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      P.eval ((m * n : ℕ) : ℚ) = P.eval (m : ℚ) * P.eval (n : ℚ)) (m : ℕ) (hm : 1 ≤ m) :
    P.eval (m : ℚ) = (m : ℚ) ^ P.natDegree := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hcomp : P.comp (C (m : ℚ) * X) = C (P.eval (m : ℚ)) * P := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + 1 : ℕ) : ℚ))
      (fun a b h => by simpa using h)
    intro n
    simp only [Set.mem_ofPred_eq, eval_comp, eval_mul, eval_C, eval_X]
    have h := hmul m (n + 1) hm (by omega)
    push_cast at h ⊢
    exact h
  have hq : (C (m : ℚ) * X).natDegree = 1 := natDegree_C_mul_X _ hm0
  have hc := coeff_comp_degree_mul_degree (p := P) (q := C (m : ℚ) * X) (by rw [hq]; norm_num)
  rw [hq, mul_one, leadingCoeff_C_mul_X, hcomp, coeff_C_mul] at hc
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  change P.eval (m : ℚ) * P.leadingCoeff = P.leadingCoeff * (m : ℚ) ^ P.natDegree at hc
  rw [mul_comm] at hc
  exact mul_left_cancel₀ hlc hc

variable {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {g : ℕ}
  {ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]} {δ : R → ℚ} {iso : R → Prop}

theorem edet_natCast (ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]) (α : R) {N : ℕ}
    (x : Fin N → ℕ) :
    edet (ρ α) (fun k => (x k : ℚ_[p])) = (ρ (aeval α (ofCoeffs x))).det := by
  rw [edet_eq, ρ_aeval, map_ofCoeffs]
  have h1 : (ρ α).map (algebraMap ℚ_[p] ℚ_[p]) = ρ α := by
    ext i j
    simp
  have h2 : (fun k => (x k : ℚ_[p])) = fun k => algebraMap ℕ ℚ_[p] (x k) := by
    funext k
    simp
  rw [h1, h2]

theorem ofCoeffs_single_zero {S : Type*} [Semiring S] {N : ℕ} (hN : 0 < N) :
    ofCoeffs (fun i : Fin N => if (i : ℕ) = 0 then (1 : S) else 0) = 1 := by
  ext m
  rw [coeff_ofCoeffs, coeff_one]
  split_ifs with h1 h2 h2 <;> simp_all

theorem edet_single_zero {T : Type*} [CommRing T] [Algebra ℚ_[p] T] {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]) :
    edet A (fun i : Fin N => if (i : ℕ) = 0 then (1 : T) else 0) = 1 := by
  rw [edet_eq, ofCoeffs_single_zero hN, map_one, Matrix.det_one]

theorem map_ofCoeffs_X {σ T : Type*} [CommRing T] [Algebra ℚ T] {N : ℕ} (f : Fin N → σ)
    (w : σ → T) :
    (ofCoeffs (fun i => (MvPolynomial.X (f i) : MvPolynomial σ ℚ))).map
      ((MvPolynomial.aeval w : MvPolynomial σ ℚ →ₐ[ℚ] T) : MvPolynomial σ ℚ →+* T) =
        ofCoeffs (fun i => w (f i)) := by
  rw [map_ofCoeffs]
  simp

variable (α : R) {M : MvPolynomial (Fin (2 * (2 * g + 1) + 1)) ℚ}

/-- Multiplicativity of `coeffEval M` in degree at most `2g + 1`. -/
theorem coeffEval_mul (hD : DegreeData ρ δ iso)
    (hM : ∀ x : Fin (2 * (2 * g + 1) + 1) → ℕ,
      δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M)
    (S : Type*) [CommRing S] [Algebra ℚ S] (F G : S[X])
    (hF : F.natDegree ≤ 2 * g + 1) (hG : G.natDegree ≤ 2 * g + 1) :
    coeffEval M (F * G) = coeffEval M F * coeffEval M G := by
  classical
  let σ := Fin (2 * g + 2) ⊕ Fin (2 * g + 2)
  let 𝔽 : (MvPolynomial σ ℚ)[X] := ofCoeffs fun i => MvPolynomial.X (Sum.inl i)
  let 𝔾 : (MvPolynomial σ ℚ)[X] := ofCoeffs fun i => MvPolynomial.X (Sum.inr i)
  have hΨ : coeffEval M (𝔽 * 𝔾) = coeffEval M 𝔽 * coeffEval M 𝔾 := by
    let A := ρ α
    let Z : MvPolynomial σ ℚ_[p] := edet A (fun i => MvPolynomial.X (Sum.inl i)) *
      edet A (fun i => MvPolynomial.X (Sum.inr i))
    have hZeval : ∀ w : σ → ℚ_[p], MvPolynomial.eval w Z =
        edet A (fun i => w (Sum.inl i)) * edet A (fun i => w (Sum.inr i)) := by
      intro w
      change MvPolynomial.aeval w Z = _
      rw [map_mul, map_edet, map_edet]
      simp
    apply eq_of_eval_natCast_of_ne_zero _ _ Z
    · intro hZ
      have h := congrArg (MvPolynomial.eval
        (Sum.elim (fun i : Fin (2 * g + 2) => if (i : ℕ) = 0 then (1 : ℚ_[p]) else 0)
          (fun i : Fin (2 * g + 2) => if (i : ℕ) = 0 then (1 : ℚ_[p]) else 0))) hZ
      rw [hZeval, map_zero] at h
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      rw [edet_single_zero (by omega), one_mul] at h
      exact one_ne_zero h
    · intro w hw
      rw [hZeval] at hw
      let Gy : ℕ[X] := ofCoeffs fun i => w (Sum.inl i)
      let Gz : ℕ[X] := ofCoeffs fun i => w (Sum.inr i)
      have hy : (ρ (aeval α Gy)).det ≠ 0 := by
        rw [← edet_natCast]; exact left_ne_zero_of_mul hw
      have hz : (ρ (aeval α Gz)).det ≠ 0 := by
        rw [← edet_natCast]; exact right_ne_zero_of_mul hw
      have hdy : Gy.natDegree < 2 * g + 2 := natDegree_ofCoeffs_lt _ (by omega)
      have hdz : Gz.natDegree < 2 * g + 2 := natDegree_ofCoeffs_lt _ (by omega)
      have hF' := map_ofCoeffs_X (Sum.inl : _ → σ) (fun s => (w s : ℚ))
      have hG' := map_ofCoeffs_X (Sum.inr : _ → σ) (fun s => (w s : ℚ))
      have hGy : ofCoeffs (fun i => ((w (Sum.inl i) : ℕ) : ℚ)) = Gy.map (algebraMap ℕ ℚ) := by
        rw [map_ofCoeffs]; simp
      have hGz : ofCoeffs (fun i => ((w (Sum.inr i) : ℕ) : ℚ)) = Gz.map (algebraMap ℕ ℚ) := by
        rw [map_ofCoeffs]; simp
      change MvPolynomial.aeval (fun s => (w s : ℚ)) _ = MvPolynomial.aeval (fun s => (w s : ℚ)) _
      rw [map_mul, ← coeffEval_map, ← coeffEval_map, ← coeffEval_map, Polynomial.map_mul,
        hF', hG', hGy, hGz, ← Polynomial.map_mul,
        coeffEval_natCast M δ α hM _ (by
          calc (Gy * Gz).natDegree ≤ Gy.natDegree + Gz.natDegree := natDegree_mul_le
            _ < 2 * (2 * g + 1) + 1 := by omega),
        coeffEval_natCast M δ α hM _ (by omega), coeffEval_natCast M δ α hM _ (by omega),
        map_mul, hD.mul _ _ (hD.iso_of_det_ne_zero hy) (hD.iso_of_det_ne_zero hz)]
      simp
  let w : σ → S := Sum.elim (fun i => F.coeff i) (fun i => G.coeff i)
  have hF' := map_ofCoeffs_X (Sum.inl : _ → σ) w
  have hG' := map_ofCoeffs_X (Sum.inr : _ → σ) w
  have hFw : ofCoeffs (fun i => w (Sum.inl i)) = F := ofCoeffs_coeff F (by omega)
  have hGw : ofCoeffs (fun i => w (Sum.inr i)) = G := ofCoeffs_coeff G (by omega)
  have h := congrArg (MvPolynomial.aeval w : MvPolynomial σ ℚ →ₐ[ℚ] S) hΨ
  rw [map_mul, ← coeffEval_map, ← coeffEval_map, ← coeffEval_map, Polynomial.map_mul,
    hF', hG', hFw, hGw] at h
  exact h

/-- `coeffEval M` on constants, as a one-variable polynomial. -/
theorem coeffEval_C_eq {N : ℕ} (M : MvPolynomial (Fin N) ℚ) {S : Type*} [CommRing S]
    [Algebra ℚ S] (t : S) :
    coeffEval M (C t) = Polynomial.aeval t
      (MvPolynomial.aeval (fun k : Fin N => if (k : ℕ) = 0 then (X : ℚ[X]) else 0) M) := by
  rw [coeffEval, MvPolynomial.comp_aeval_apply]
  refine congrArg (fun v => MvPolynomial.aeval v M) (funext fun k => ?_)
  rw [coeff_C]
  split_ifs <;> simp

/-- `coeffEval M` on a line `C a + C b * X`, as a one-variable polynomial in the parameter. -/
theorem coeffEval_line_eq {N : ℕ} (M : MvPolynomial (Fin N) ℚ) (u v : ℚ[X]) {S : Type*}
    [CommRing S] [Algebra ℚ S] (t : S) :
    coeffEval M (C (Polynomial.aeval t u) + C (Polynomial.aeval t v) * X) = Polynomial.aeval t
      (MvPolynomial.aeval (fun k : Fin N => if (k : ℕ) = 0 then u else if (k : ℕ) = 1 then v
        else 0) M) := by
  rw [coeffEval, MvPolynomial.comp_aeval_apply]
  refine congrArg (fun w => MvPolynomial.aeval w M) (funext fun k => ?_)
  rw [coeff_add, coeff_C, coeff_C_mul]
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · rw [coeff_X_of_ne_one h1]
    simp

/-- The `ρ`-determinant of a natural number. -/
theorem det_natCast (ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]) (n : ℕ) :
    (ρ (n : R)).det = (n : ℚ_[p]) ^ (2 * g) := by
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[p] (Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p])),
    Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

/-- The degree of multiplication by a positive integer `n` is `n ^ (2g)`. -/
theorem DegreeData.δ_natCast (hD : DegreeData ρ δ iso) (n : ℕ) (hn : 1 ≤ n) :
    δ (n : R) = (n : ℚ) ^ (2 * g) := by
  have hiso : ∀ m : ℕ, 1 ≤ m → iso (m : R) := fun m hm =>
    hD.iso_of_det_ne_zero (by
      rw [det_natCast]
      exact pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)))
  obtain ⟨P, -, hP⟩ := hD.line 1 0
  have hPδ : ∀ m : ℕ, P.eval (m : ℚ) = δ (m : R) := fun m => by rw [← hP m, add_zero, nsmul_one]
  have hP0 : P ≠ 0 := by
    intro h0
    have h1 := hD.norm 1 (by simpa using hiso 1 le_rfl)
    have hδ1 : δ (1 : R) = 0 := by
      have := hPδ 1
      rw [Nat.cast_one, Nat.cast_one, h0, eval_zero] at this
      exact this.symm
    rw [hδ1, map_one, Matrix.det_one] at h1
    simp at h1
  have hpow := eval_natCast_eq_pow_of_mul P hP0 (fun a b ha hb => by
    rw [hPδ, hPδ, hPδ, Nat.cast_mul, hD.mul _ _ (hiso a ha) (hiso b hb)])
  have hj : P.natDegree = 2 * g := by
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    have h := hD.norm (p : R) (hiso p hp1)
    rw [← hPδ, hpow p hp1, det_natCast] at h
    push_cast at h
    rw [norm_pow, norm_pow, Padic.norm_p] at h
    have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      positivity
    have hp1' : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    exact (pow_right_strictAnti₀ hp0 hp1').injective h
  rw [← hPδ, hpow n hn, hj]

/-- On constants, `coeffEval M` is the `2g`-th power. -/
theorem coeffEval_C (hD : DegreeData ρ δ iso)
    (hM : ∀ x : Fin (2 * (2 * g + 1) + 1) → ℕ,
      δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M)
    (S : Type*) [CommRing S] [Algebra ℚ S] (c : S) :
    coeffEval M (C c) = c ^ (2 * g) := by
  have hΓX : MvPolynomial.aeval
      (fun k : Fin (2 * (2 * g + 1) + 1) => if (k : ℕ) = 0 then (X : ℚ[X]) else 0) M =
        X ^ (2 * g) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + 1 : ℕ) : ℚ))
      (fun a b h => by simpa using h)
    intro n
    simp only [Set.mem_ofPred_eq]
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [eval_pow, eval_X, ← Polynomial.coe_aeval_eq_eval, ← coeffEval_C_eq,
      ← hD.δ_natCast (n + 1) (by omega)]
    have h := coeffEval_natCast M δ α hM (S := ℚ) (C (n + 1 : ℕ)) (by rw [natDegree_C]; omega)
    rw [Polynomial.map_C] at h
    rw [show ((n + 1 : ℕ) : ℚ) = algebraMap ℕ ℚ (n + 1) by simp, h]
    simp
  rw [coeffEval_C_eq, hΓX, map_pow, aeval_X]

/-- The polynomial `x ↦ coeffEval M (C x + X)`. -/
def linePt {N : ℕ} (M : MvPolynomial (Fin N) ℚ) : ℚ[X] :=
  MvPolynomial.aeval (fun k : Fin N => if (k : ℕ) = 0 then (X : ℚ[X]) else if (k : ℕ) = 1 then 1
    else 0) M

/-- The characteristic polynomial `x ↦ coeffEval M (X - C x)` of the degree function. -/
def lineQ {N : ℕ} (M : MvPolynomial (Fin N) ℚ) : ℚ[X] := (linePt M).comp (-X)

theorem coeffEval_X_sub_C {N : ℕ} (M : MvPolynomial (Fin N) ℚ) {S : Type*} [CommRing S]
    [Algebra ℚ S] (x : S) : coeffEval M (X - C x) = Polynomial.aeval x (lineQ M) := by
  rw [lineQ, Polynomial.aeval_comp, linePt, ← coeffEval_line_eq]
  congr 1
  simp only [map_neg, aeval_X, map_one, one_mul]
  ring

theorem linePt_monic (hD : DegreeData ρ δ iso)
    (hM : ∀ x : Fin (2 * (2 * g + 1) + 1) → ℕ,
      δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M) :
    (linePt M).Monic ∧ (linePt M).natDegree = 2 * g := by
  let R₁ : ℚ[X] := MvPolynomial.aeval
    (fun k : Fin (2 * (2 * g + 1) + 1) => if (k : ℕ) = 0 then (1 : ℚ[X]) else
      if (k : ℕ) = 1 then X else 0) M
  have hR₁ : ∀ y : ℚ, R₁.eval y = coeffEval M (C 1 + C y * X) := by
    intro y
    rw [← Polynomial.coe_aeval_eq_eval]
    simp only [R₁]
    rw [← coeffEval_line_eq]
    simp
  have hPt : ∀ x : ℚ, (linePt M).eval x = coeffEval M (C x + C 1 * X) := by
    intro x
    rw [← Polynomial.coe_aeval_eq_eval, linePt, ← coeffEval_line_eq]
    simp
  have hinf : Set.Infinite (Set.range fun n : ℕ => ((n : ℕ) : ℚ)) :=
    Set.infinite_range_of_injective Nat.cast_injective
  -- degree bound for `linePt` from the line `n • 1 + α`
  have hdegPt : (linePt M).natDegree ≤ 2 * g := by
    obtain ⟨P, hP, hPe⟩ := hD.line 1 α
    have : linePt M = P := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine hinf.mono ?_
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [hPt, ← hPe n]
      have h := coeffEval_natCast M δ α hM (S := ℚ) (C n + X)
        (by
          calc (C n + X : ℕ[X]).natDegree ≤ max (C n : ℕ[X]).natDegree (X : ℕ[X]).natDegree :=
                natDegree_add_le _ _
            _ ≤ 1 := by simp
            _ < _ := by omega)
      rw [Polynomial.map_add, Polynomial.map_C, Polynomial.map_X] at h
      rw [show (C (n : ℚ) + C 1 * X) = C (algebraMap ℕ ℚ n) + X by simp, h]
      simp [add_comm]
    rw [this]
    exact hP
  have hdegR₁ : R₁.natDegree ≤ 2 * g := by
    obtain ⟨P, hP, hPe⟩ := hD.line α 1
    have : R₁ = P := by
      apply Polynomial.eq_of_infinite_eval_eq
      refine hinf.mono ?_
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [hR₁, ← hPe n]
      have h := coeffEval_natCast M δ α hM (S := ℚ) (C 1 + C n * X)
        (by
          calc (C 1 + C n * X : ℕ[X]).natDegree
              ≤ max (C 1 : ℕ[X]).natDegree (C n * X : ℕ[X]).natDegree := natDegree_add_le _ _
            _ ≤ 1 := by
              refine max_le (by simp) ?_
              exact (natDegree_C_mul_le _ _).trans (by simp)
            _ < _ := by omega)
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_X] at h
      rw [show (C (1 : ℚ) + C (n : ℚ) * X) = C (algebraMap ℕ ℚ 1) + C (algebraMap ℕ ℚ n) * X
        by simp, h]
      simp [nsmul_eq_mul, add_comm]
    rw [this]
    exact hP
  have hR₁0 : R₁.eval 0 = 1 := by
    rw [hR₁, C_0, zero_mul, add_zero, coeffEval_C α hD hM, one_pow]
  have hrel : ∀ x : ℚ, x ≠ 0 → (linePt M).eval x = x ^ (2 * g) * R₁.eval x⁻¹ := by
    intro x hx
    rw [hPt, hR₁, ← coeffEval_C α hD hM ℚ x, ← coeffEval_mul α hD hM ℚ _ _ (by simp)]
    · congr 1
      rw [mul_add, ← C_mul, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hx]
    · calc (C (1 : ℚ) + C x⁻¹ * X).natDegree
          ≤ max (C (1 : ℚ)).natDegree (C x⁻¹ * X).natDegree := natDegree_add_le _ _
        _ ≤ 1 := by
          refine max_le (by simp) ?_
          exact (natDegree_C_mul_le _ _).trans (by simp)
        _ ≤ 2 * g + 1 := by omega
  have hreflect : linePt M = reflect (2 * g) R₁ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective (f := fun n : ℕ => ((n + 1 : ℕ) : ℚ))
      (fun a b h => by simpa using h)).mono ?_
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have hx : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hrel _ hx]
    let _ : Invertible (((n + 1 : ℕ) : ℚ)⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
    have h := eval₂_reflect_mul_pow (RingHom.id ℚ) (((n + 1 : ℕ) : ℚ)⁻¹) (2 * g) R₁ hdegR₁
    rw [invOf_eq_inv, inv_inv] at h
    rw [← eval₂_id, ← eval₂_id, ← h, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hx, one_pow,
      mul_one]
  have hcoeff : (linePt M).coeff (2 * g) = 1 := by
    rw [hreflect, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero, hR₁0]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hdegPt hcoeff,
    natDegree_eq_of_le_of_coeff_ne_zero hdegPt (by rw [hcoeff]; exact one_ne_zero)⟩

theorem lineQ_monic (hD : DegreeData ρ δ iso)
    (hM : ∀ x : Fin (2 * (2 * g + 1) + 1) → ℕ,
      δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M) :
    (lineQ M).Monic ∧ (lineQ M).natDegree = 2 * g := by
  obtain ⟨hmon, hdeg⟩ := linePt_monic α hD hM
  have hX : (-X : ℚ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  refine ⟨?_, ?_⟩
  · rw [Monic, lineQ, leadingCoeff_comp (by rw [hX]; exact one_ne_zero), hmon.leadingCoeff,
      leadingCoeff_neg, leadingCoeff_X, hdeg, one_mul, pow_mul]
    simp
  · rw [lineQ, natDegree_comp, hX, hdeg, mul_one]

end Main

end Langlands.Algebra.DegreeDeterminant
