import Langlands.Shimura.Unitary.KottwitzPolynomial

/-!
# The Frobenius action on the diagonal torus of the dual group

The action `σ = dualAction G` of `G ∈ CMPerm S` on `Ĝ = GL₁ × ∏_τ GL_n` preserves the
diagonal torus. This file computes it in the torus coordinates `(ζ, (s_{τ,k}))` used by
`torusElement`, computes its transpose on cocharacters in the free coordinates
`(a₀, (a_{τ,k}))` used by `cocharPairing`, and deduces the same two formulas for the
norm `N_f(t̂) = t̂ · σ(t̂) ⋯ σ^{f-1}(t̂)` (`frobNorm`). See the paired Markdown.
-/

noncomputable section

namespace Langlands.Shimura.KottwitzDual

universe u v

section Torus

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L]

theorem det_diagUnit (s : Fin n → Lˣ) :
    Matrix.GeneralLinearGroup.det (diagUnit (L := L) s) = ∏ j, s j := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, diagUnit_val, Matrix.det_diagonal]

omit [Fintype S] in
theorem signedAntidiagonal_mul_diagonal_mul_transpose (d : Fin n → L) :
    signedAntidiagonal n L * Matrix.diagonal d * (signedAntidiagonal n L).transpose =
      Matrix.diagonal (fun k => d (Fin.rev k)) := by
  ext k l
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev k)]
  · rw [Matrix.mul_diagonal]
    simp only [Matrix.transpose_apply, signedAntidiagonal, Matrix.diagonal_apply]
    by_cases h : k = l
    · subst h
      have h1 : ((-1 : L) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      simp only [ite_true]
      linear_combination d (Fin.rev k) * h1
    · have : Fin.rev k ≠ Fin.rev l := fun e => h (Fin.rev_injective e)
      simp [h, this]
  · intro j _ hj
    rw [Matrix.mul_diagonal]
    simp [signedAntidiagonal, hj]
  · simp

omit [Fintype S] in
/-- The pinned involution on the diagonal torus: `θ(diag s) = diag(k ↦ s_{rev k}⁻¹)`. -/
theorem twist_diagUnit (s : Fin n → Lˣ) :
    twist n L (diagUnit s) = diagUnit (fun k => (s (Fin.rev k))⁻¹) := by
  apply Units.ext
  rw [twist_apply, Units.val_mul, Units.val_mul, transposeInv_val]
  have hJ : ((signedAntidiagonalUnit n L)⁻¹ : GL (Fin n) L).val =
      (signedAntidiagonal n L).transpose := rfl
  have hJ' : (signedAntidiagonalUnit n L : GL (Fin n) L).val = signedAntidiagonal n L := rfl
  have hs : ((diagUnit s)⁻¹ : GL (Fin n) L).val =
      Matrix.diagonal (fun j => (((s j)⁻¹ : Lˣ) : L)) := rfl
  rw [hJ, hJ', hs, Matrix.diagonal_transpose, diagUnit_val,
    signedAntidiagonal_mul_diagonal_mul_transpose]

omit [Fintype S] in
theorem torusElement_one : torusElement (1 : Lˣ × (S → Fin n → Lˣ)) = 1 := by
  ext1
  · rfl
  · funext τ
    ext : 1
    simp [torusElement, diagUnit_val]

/-- The torus coordinates of `G · t̂`, for `t̂ = (ζ, (diag s_τ)_τ)`. -/
def torusTwist (G : CMPerm S) (t : Lˣ × (S → Fin n → Lˣ)) : Lˣ × (S → Fin n → Lˣ) :=
  (t.1 * ∏ τ, (if CMPerm.crosses G τ then ∏ j, t.2 τ j else 1),
    fun τ' => if CMPerm.crosses G ((CMPerm.base G).symm τ') then
      (fun k => (t.2 ((CMPerm.base G).symm τ') (Fin.rev k))⁻¹)
      else t.2 ((CMPerm.base G).symm τ'))

/-- `G` preserves the diagonal torus of `Ĝ`. -/
theorem dualEndo_torusElement (G : CMPerm S) (t : Lˣ × (S → Fin n → Lˣ)) :
    dualEndo G (torusElement t) = torusElement (torusTwist G t) := by
  ext1
  · rw [dualEndo_fst]
    simp only [torusElement, torusTwist]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    split_ifs
    · exact det_diagUnit _
    · rfl
  · funext τ'
    rw [dualEndo_snd]
    simp only [torusElement, torusTwist]
    split_ifs
    · exact twist_diagUnit _
    · rfl

variable (n) in
/-- The transpose of the action of `G` on cocharacters in the free coordinates
`(a₀, (a_{τ,k}))`: `cocharPairing (G · t̂) a = cocharPairing t̂ (G^* a)`. -/
def cocharPullback (G : CMPerm S) : (ℤ × (S → Fin n → ℤ)) →+ (ℤ × (S → Fin n → ℤ)) where
  toFun a := (a.1, fun τ k => if CMPerm.crosses G τ then a.1 - a.2 (CMPerm.base G τ) (Fin.rev k)
    else a.2 (CMPerm.base G τ) k)
  map_zero' := by
    ext τ k
    · rfl
    · simp
  map_add' a b := by
    ext τ k
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      split_ifs <;> ring

omit [Fintype S] in
theorem cocharPullback_apply (G : CMPerm S) (a : ℤ × (S → Fin n → ℤ)) :
    cocharPullback n G a = (a.1, fun τ k => if CMPerm.crosses G τ then
      a.1 - a.2 (CMPerm.base G τ) (Fin.rev k) else a.2 (CMPerm.base G τ) k) := rfl

omit [Fintype S] in
theorem cocharPullback_one (a : ℤ × (S → Fin n → ℤ)) :
    cocharPullback n (1 : CMPerm S) a = a := by
  rw [cocharPullback_apply]
  ext τ k
  · rfl
  · simp [CMPerm.crosses_one]

omit [Fintype S] in
/-- The pullback is contravariant: `(G H)^* = H^* ∘ G^*`. -/
theorem cocharPullback_mul (G H : CMPerm S) (a : ℤ × (S → Fin n → ℤ)) :
    cocharPullback n (G * H) a = cocharPullback n H (cocharPullback n G a) := by
  simp only [cocharPullback_apply]
  ext τ k
  · rfl
  · simp only [CMPerm.crosses_mul, CMPerm.base_apply, CMPerm.baseFun_mul]
    by_cases hH : CMPerm.crosses H τ = true <;>
      by_cases hG : CMPerm.crosses G (CMPerm.baseFun H τ) = true <;> simp [hH, hG, Fin.rev_rev]

omit [Fintype S] in
theorem cocharPullback_pow (G : CMPerm S) (r : ℕ) (a : ℤ × (S → Fin n → ℤ)) :
    cocharPullback n (G ^ r) a = (cocharPullback n G)^[r] a := by
  induction r generalizing a with
  | zero => exact cocharPullback_one a
  | succ r ih => rw [pow_succ', cocharPullback_mul, ih, Function.iterate_succ_apply]

theorem cocharPairing_add (t : Lˣ × (S → Fin n → Lˣ)) (a b : ℤ × (S → Fin n → ℤ)) :
    cocharPairing t (a + b) = cocharPairing t a * cocharPairing t b := by
  simp only [cocharPairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, zpow_add,
    Finset.prod_mul_distrib]
  ac_rfl

theorem cocharPairing_zero (t : Lˣ × (S → Fin n → Lˣ)) :
    cocharPairing t (0 : ℤ × (S → Fin n → ℤ)) = 1 := by
  simp [cocharPairing]

theorem cocharPairing_one (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (1 : Lˣ × (S → Fin n → Lˣ)) a = 1 := by
  simp [cocharPairing]

theorem cocharPairing_sum {ι : Type*} (t : Lˣ × (S → Fin n → Lˣ)) (s : Finset ι)
    (a : ι → ℤ × (S → Fin n → ℤ)) :
    cocharPairing t (∑ i ∈ s, a i) = ∏ i ∈ s, cocharPairing t (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cocharPairing_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, cocharPairing_add, ih]

theorem cocharPairing_prod {ι : Type*} (t : ι → Lˣ × (S → Fin n → Lˣ)) (s : Finset ι)
    (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (∏ i ∈ s, t i) a = ∏ i ∈ s, cocharPairing (t i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cocharPairing_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, cocharPairing_mul, ih]

theorem cocharPairing_torusTwist (G : CMPerm S) (t : Lˣ × (S → Fin n → Lˣ))
    (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (torusTwist G t) a = cocharPairing t (cocharPullback n G a) := by
  rw [cocharPullback_apply]
  simp only [cocharPairing, torusTwist]
  rw [← Equiv.prod_comp (CMPerm.base G) (fun τ' => ∏ k, (if CMPerm.crosses G
    ((CMPerm.base G).symm τ') then (fun k => (t.2 ((CMPerm.base G).symm τ') (Fin.rev k))⁻¹)
      else t.2 ((CMPerm.base G).symm τ')) k ^ a.2 τ' k)]
  simp only [Equiv.symm_apply_apply]
  rw [mul_zpow, mul_assoc, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  split_ifs with hc
  · beta_reduce
    rw [← Finset.prod_zpow, Fintype.prod_equiv Fin.revPerm
      (fun k => (t.2 τ (Fin.rev k))⁻¹ ^ a.2 (CMPerm.base G τ) k)
      (fun k => (t.2 τ k)⁻¹ ^ a.2 (CMPerm.base G τ) (Fin.rev k)) (fun k => by simp),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_zpow, zpow_sub]
  · simp

/-- `N(t̂) = t̂ · σ(t̂) ⋯ σ^{f-1}(t̂)` in torus coordinates. -/
def torusNorm (G : CMPerm S) (t : Lˣ × (S → Fin n → Lˣ)) (f : ℕ) : Lˣ × (S → Fin n → Lˣ) :=
  ∏ r ∈ Finset.range f, torusTwist (G ^ r) t

variable (n) in
/-- The transpose `N^* a = Σ_{r < f} (G^r)^* a` of the norm map on cocharacters. -/
def normCochar (G : CMPerm S) (f : ℕ) (a : ℤ × (S → Fin n → ℤ)) : ℤ × (S → Fin n → ℤ) :=
  ∑ r ∈ Finset.range f, cocharPullback n (G ^ r) a

theorem frobNorm_torusElement (G : CMPerm S) (t : Lˣ × (S → Fin n → Lˣ)) (f : ℕ) :
    frobNorm G (torusElement t) f = torusElement (torusNorm G t f) := by
  induction f with
  | zero => rw [frobNorm_zero, torusNorm, Finset.prod_range_zero, torusElement_one]
  | succ f ih =>
    rw [frobNorm_succ, ih]
    simp only [torusNorm]
    rw [Finset.prod_range_succ, torusElement_mul, ← map_pow, dualAction_apply,
      dualEndo_torusElement]

theorem cocharPairing_torusNorm (G : CMPerm S) (t : Lˣ × (S → Fin n → Lˣ)) (f : ℕ)
    (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (torusNorm G t f) a = cocharPairing t (normCochar n G f a) := by
  rw [torusNorm, normCochar, cocharPairing_prod, cocharPairing_sum]
  exact Finset.prod_congr rfl fun r _ => cocharPairing_torusTwist _ _ _

end Torus

end Langlands.Shimura.KottwitzDual
