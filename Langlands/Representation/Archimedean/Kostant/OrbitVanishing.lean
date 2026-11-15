import Langlands.Representation.Archimedean.Kostant.Coadjoint
import Langlands.Representation.Archimedean.Kostant.NilpotentConjugacy
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# The orbit statement

Proof of `OrbitVanishingStatement`.
-/

noncomputable section

set_option autoImplicit false

-- Entries of tuples of matrices are applied through the `Matrix` definition.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

/-- The coadjoint derivation on a variable, written out. -/
theorem coadDer_X_mk (x : GLProd ℂ n) (j : ι) (r q : Fin (n j)) :
    coadDer ℂ n x (X ⟨j, r, q⟩) =
      ∑ a, x j a r • (X ⟨j, a, q⟩ : MvPolynomial (Coord n) ℂ) -
        ∑ b, x j q b • (X ⟨j, r, b⟩ : MvPolynomial (Coord n) ℂ) := by
  rw [coadDer_X, lie_unit]
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.smul_apply, unit_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_smul,
    Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm, Finset.sum_comm (γ := Coord n)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem coadDer_unit_X_of_ne (i : ι) (a b : Fin (n i)) {j : ι} (h : j ≠ i) (r q : Fin (n j)) :
    coadDer ℂ n (unit ℂ n i a b) (X ⟨j, r, q⟩) = 0 := by
  rw [coadDer_X_mk]
  simp [unit, Pi.single_eq_of_ne h]

theorem coadDer_unit_X_same (i : ι) (a b r q : Fin (n i)) :
    coadDer ℂ n (unit ℂ n i a b) (X ⟨i, r, q⟩) =
      (if r = b then (X ⟨i, a, q⟩ : MvPolynomial (Coord n) ℂ) else 0) -
        (if q = a then (X ⟨i, r, b⟩ : MvPolynomial (Coord n) ℂ) else 0) := by
  rw [coadDer_X_mk]
  simp only [unit, Pi.single_eq_same, Matrix.single_apply, ite_smul, one_smul, zero_smul]
  congr 1
  · by_cases hr : r = b
    · subst hr; simp
    · simp [hr, Ne.symm hr]
  · by_cases hq : q = a
    · subst hq; simp
    · simp [hq, Ne.symm hq]

/-- Entries of `(1 + t E_ba) Y (1 - t E_ba)` for `a ≠ b`. -/
theorem transvection_conj_apply {m : ℕ} {R : Type*} [CommRing R] (Y : Matrix (Fin m) (Fin m) R)
    {a b : Fin m} (hab : a ≠ b) (t : R) (r q : Fin m) :
    (Matrix.transvection b a t * Y * Matrix.transvection b a (-t)) r q =
      Y r q + (if r = b then t * Y a q else 0) - (if q = a then t * Y r b else 0) -
        (if r = b ∧ q = a then t ^ 2 * Y a b else 0) := by
  by_cases hq : q = a
  · subst hq
    rw [Matrix.mul_transvection_apply_same]
    by_cases hr : r = b
    · subst hr
      rw [Matrix.transvection_mul_apply_same, Matrix.transvection_mul_apply_same]
      simp only [ite_true, and_self]
      ring
    · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hr,
        Matrix.transvection_mul_apply_of_ne _ _ _ _ hr]
      simp only [hr, ite_true, ite_false, false_and]
      ring
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hq]
    by_cases hr : r = b
    · subst hr
      rw [Matrix.transvection_mul_apply_same]
      simp only [hq, ite_true, ite_false, and_false]
      ring
    · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hr]
      simp [hr, hq]

/-- The point of `Coord n → ℂ` given by a tuple of matrices. -/
def tuplePoint (Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) : Coord n → ℂ :=
  fun v => Y v.1 v.2.1 v.2.2

/-- The common zero set of a space of polynomials, as a set of tuples of matrices. -/
def zeroSet (W : Submodule ℂ (MvPolynomial (Coord n) ℂ)) :
    Set (∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) :=
  {Y | ∀ f ∈ W, eval (tuplePoint n Y) f = 0}

/-- The tuple `Y` with block `i` replaced by `(1 + s E_ba) Y_i (1 - s E_ba)`, over `ℂ[s]`. -/
def flowTuple (Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (i : ι) (a b : Fin (n i)) :
    ∀ j, Matrix (Fin (n j)) (Fin (n j)) (Polynomial ℂ) :=
  Function.update (fun j => (Y j).map Polynomial.C) i
    (Matrix.transvection b a Polynomial.X * (Y i).map Polynomial.C *
      Matrix.transvection b a (-Polynomial.X))

/-- Evaluation of polynomials along the flow. -/
def flowEval (Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (i : ι) (a b : Fin (n i)) :
    MvPolynomial (Coord n) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun v : Coord n => flowTuple n Y i a b v.1 v.2.1 v.2.2

omit [Fintype ι] in
theorem eval_flowEval (Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (i : ι) {a b : Fin (n i)}
    (hab : a ≠ b) (s : ℂ) (f : MvPolynomial (Coord n) ℂ) :
    (flowEval n Y i a b f).eval s =
      eval (tuplePoint n (Function.update Y i
        (Matrix.transvection b a s * Y i * Matrix.transvection b a (-s)))) f := by
  have h : (Polynomial.aeval s).comp (flowEval n Y i a b) =
      aeval (tuplePoint n (Function.update Y i
        (Matrix.transvection b a s * Y i * Matrix.transvection b a (-s)))) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨j, r, q⟩ := v
    simp only [AlgHom.comp_apply, flowEval, aeval_X, tuplePoint]
    by_cases h : j = i
    · subst h
      simp only [flowTuple, Function.update_self, Polynomial.coe_aeval_eq_eval]
      rw [transvection_conj_apply _ hab, transvection_conj_apply _ hab]
      simp only [Matrix.map_apply, Polynomial.eval_sub, Polynomial.eval_add,
        apply_ite (Polynomial.eval s), Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero]
    · simp [flowTuple, Function.update_of_ne h, Matrix.map_apply]
  have := congrArg (fun φ => φ f) h
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, coe_aeval_eq_eval] using this

theorem derivative_flowEval (Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (i : ι) {a b : Fin (n i)}
    (hab : a ≠ b) (f : MvPolynomial (Coord n) ℂ) :
    Polynomial.derivative (flowEval n Y i a b f) =
      flowEval n Y i a b (coadDer ℂ n (unit ℂ n i a b) f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, AlgHom.commutes]
    simp
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul]
    suffices hv : Polynomial.derivative (flowEval n Y i a b (X v)) =
        flowEval n Y i a b (coadDer ℂ n (unit ℂ n i a b) (X v)) by
      rw [hv]; ring
    obtain ⟨j, r, q⟩ := v
    by_cases h : j = i
    · subst h
      rw [coadDer_unit_X_same]
      simp only [flowEval, aeval_X, map_sub, apply_ite (aeval _), map_zero, flowTuple,
        Function.update_self]
      rw [transvection_conj_apply _ hab, transvection_conj_apply _ hab,
        transvection_conj_apply _ hab]
      by_cases hr : r = b <;> by_cases hq : q = a <;>
        simp [hr, hq, hab, Ne.symm hab, Matrix.map_apply]; ring
    · rw [coadDer_unit_X_of_ne n i a b h]
      simp [flowEval, flowTuple, Function.update_of_ne h, Matrix.map_apply]

/-- The zero set of a stable space is invariant under conjugating block `i` by the transvection
`1 + s E_ba`, `a ≠ b`. -/
theorem update_transvection_mem_zeroSet {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)} {i : ι}
    {a b : Fin (n i)} (hab : a ≠ b) (hW : ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    {Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ} (hY : Y ∈ zeroSet n W) (s : ℂ) :
    Function.update Y i (Matrix.transvection b a s * Y i * Matrix.transvection b a (-s)) ∈
      zeroSet n W := by
  intro f hf
  rw [← eval_flowEval n Y i hab s f]
  have hmem : ∀ k, (⇑(coadDer ℂ n (unit ℂ n i a b)))^[k] f ∈ W := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih => rw [Function.iterate_succ_apply']; exact hW _ ih
  have hder : ∀ k, (⇑Polynomial.derivative)^[k] (flowEval n Y i a b f) =
      flowEval n Y i a b ((⇑(coadDer ℂ n (unit ℂ n i a b)))^[k] f) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, derivative_flowEval n Y i hab,
        ← Function.iterate_succ_apply' (⇑(coadDer ℂ n (unit ℂ n i a b)))]
  have h0 : ∀ g ∈ W, (flowEval n Y i a b g).eval 0 = 0 := by
    intro g hg
    rw [eval_flowEval n Y i hab, neg_zero, Matrix.transvection_zero, one_mul, mul_one,
      Function.update_eq_self]
    exact hY g hg
  have hzero : flowEval n Y i a b f = 0 := by
    ext k
    have h := Polynomial.coeff_iterate_derivative (k := k) (flowEval n Y i a b f) 0
    rw [hder, Polynomial.coeff_zero_eq_eval_zero, h0 _ (hmem k), zero_add,
      Nat.descFactorial_self, nsmul_eq_mul] at h
    rw [Polynomial.coeff_zero]
    exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast k.factorial_ne_zero)
  rw [hzero, Polynomial.eval_zero]

theorem transvection_mul_apply' {m : ℕ} {R : Type*} [CommRing R] (k l : Fin m) (c : R)
    (M : Matrix (Fin m) (Fin m) R) (r q : Fin m) :
    (Matrix.transvection k l c * M) r q = M r q + if r = k then c * M l q else 0 := by
  by_cases h : r = k
  · subst h; simp
  · simp [Matrix.transvection_mul_apply_of_ne _ _ _ _ h, h]

theorem transvection_apply' {m : ℕ} {R : Type*} [CommRing R] (k l : Fin m) (c : R)
    (r q : Fin m) :
    Matrix.transvection k l c r q = (if r = q then 1 else 0) + if r = k ∧ q = l then c else 0 := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  exact if_congr (and_congr eq_comm eq_comm) rfl rfl

/-- `diag(t, t⁻¹) = (1 + (t-1)E_kl)(1 + E_lk)(1 + (t⁻¹-1)E_kl)(1 - tE_lk)` in the `k, l` plane. -/
theorem diagonal_eq_transvection_mul {m : ℕ} {K : Type*} [Field K] {k l : Fin m} (hkl : k ≠ l)
    {t : K} (ht : t ≠ 0) :
    Matrix.diagonal (fun r => if r = k then t else if r = l then t⁻¹ else 1) =
      Matrix.transvection k l (t - 1) * (Matrix.transvection l k 1 *
        (Matrix.transvection k l (t⁻¹ - 1) * Matrix.transvection l k (-t))) := by
  have hlk : l ≠ k := Ne.symm hkl
  ext r q
  simp only [transvection_mul_apply', Matrix.diagonal_apply, transvection_apply', hkl, hlk,
    ite_true, ite_false, true_and, false_and]
  rcases eq_or_ne r k with rfl | hrk
  · rcases eq_or_ne q r with rfl | hqr
    · simp [hkl]; field_simp; ring
    · rcases eq_or_ne q l with rfl | hql
      · simp [hkl, hqr]; field_simp; ring
      · simp [hkl, hqr, Ne.symm hqr, Ne.symm hql]
  · rcases eq_or_ne r l with rfl | hrl
    · rcases eq_or_ne q r with rfl | hqr
      · simp [hkl, hlk]
      · rcases eq_or_ne q k with rfl | hqk
        · simp [hrk]; field_simp; ring
        · simp [hlk, hqk, Ne.symm hqr, Ne.symm hqk]
    · simp [hrk, hrl]

/-- Conjugating block `i` by `g` preserves the zero set of `W`. -/
def PreservesZeroSet (W : Submodule ℂ (MvPolynomial (Coord n) ℂ)) (i : ι)
    (g : Matrix (Fin (n i)) (Fin (n i)) ℂ) : Prop :=
  ∀ Y ∈ zeroSet n W, Function.update Y i (g * Y i * g⁻¹) ∈ zeroSet n W

section Invariance

variable {n}

omit [Fintype ι] in
theorem PreservesZeroSet.mul {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)} {i : ι}
    {g h : Matrix (Fin (n i)) (Fin (n i)) ℂ} (hg : PreservesZeroSet n W i g)
    (hh : PreservesZeroSet n W i h) : PreservesZeroSet n W i (g * h) := by
  intro Y hY
  have := hg _ (hh Y hY)
  rw [Function.update_idem, Function.update_self] at this
  simpa only [Matrix.mul_inv_rev, Matrix.mul_assoc] using this

omit [Fintype ι] in
theorem preservesZeroSet_one (W : Submodule ℂ (MvPolynomial (Coord n) ℂ)) (i : ι) :
    PreservesZeroSet n W i 1 := by
  intro Y hY
  rwa [inv_one, one_mul, mul_one, Function.update_eq_self]

omit [Fintype ι] in
theorem PreservesZeroSet.smul {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)} {i : ι}
    {g : Matrix (Fin (n i)) (Fin (n i)) ℂ} (hg : PreservesZeroSet n W i g) (hdet : IsUnit g.det)
    {c : ℂ} (hc : c ≠ 0) : PreservesZeroSet n W i (c • g) := by
  have hinv : (c • g)⁻¹ = c⁻¹ • g⁻¹ := Matrix.inv_eq_right_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hdet,
      mul_inv_cancel₀ hc, one_smul])
  intro Y hY
  rw [hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact hg Y hY

theorem preservesZeroSet_transvection {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)}
    (hW : ∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    (i : ι) {k l : Fin (n i)} (hkl : k ≠ l) (c : ℂ) :
    PreservesZeroSet n W i (Matrix.transvection k l c) := by
  have hinv : (Matrix.transvection k l c)⁻¹ = Matrix.transvection k l (-c) :=
    Matrix.inv_eq_right_inv (by
      rw [Matrix.transvection_mul_transvection_same _ _ hkl, add_neg_cancel,
        Matrix.transvection_zero])
  intro Y hY
  rw [hinv]
  exact update_transvection_mem_zeroSet n (Ne.symm hkl) (hW i l k (Ne.symm hkl)) hY c

theorem preservesZeroSet_diagonal_pair {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)}
    (hW : ∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    (i : ι) {k l : Fin (n i)} (hkl : k ≠ l) {t : ℂ} (ht : t ≠ 0) :
    PreservesZeroSet n W i
      (Matrix.diagonal fun r => if r = k then t else if r = l then t⁻¹ else 1) := by
  rw [diagonal_eq_transvection_mul hkl ht]
  exact (preservesZeroSet_transvection hW i hkl _).mul
    ((preservesZeroSet_transvection hW i (Ne.symm hkl) _).mul
      ((preservesZeroSet_transvection hW i hkl _).mul
        (preservesZeroSet_transvection hW i (Ne.symm hkl) _)))

/-- Diagonal matrices of determinant one preserve the zero set. -/
theorem preservesZeroSet_diagonal_of_prod_eq_one {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)}
    (hW : ∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    (i : ι) (l0 : Fin (n i)) (D : Fin (n i) → ℂ) (hD : ∏ r, D r = 1) :
    PreservesZeroSet n W i (Matrix.diagonal D) := by
  have hD0 : ∀ r, D r ≠ 0 := fun r h0 => by
    rw [Finset.prod_eq_zero (Finset.mem_univ r) h0] at hD
    exact zero_ne_one hD
  have key : ∀ s : Finset (Fin (n i)), l0 ∉ s → PreservesZeroSet n W i
      (Matrix.diagonal fun r => if r ∈ s then D r else if r = l0 then ∏ k ∈ s, (D k)⁻¹ else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using preservesZeroSet_one W i
    | insert k s hks ih =>
      intro hl
      have hkl : k ≠ l0 := fun h => hl (h ▸ Finset.mem_insert_self k s)
      have hls : l0 ∉ s := fun h => hl (Finset.mem_insert_of_mem h)
      have h := (preservesZeroSet_diagonal_pair hW i hkl (hD0 k)).mul (ih hls)
      rw [Matrix.diagonal_mul_diagonal] at h
      convert h using 2
      funext r
      rw [Finset.prod_insert hks]
      by_cases hrk : r = k
      · subst hrk; simp [hks, hkl]
      · by_cases hrs : r ∈ s
        · have hrl : r ≠ l0 := fun h => hls (h ▸ hrs)
          simp [hrk, hrs, hrl]
        · by_cases hrl : r = l0
          · simp [hrl, hls, Ne.symm hkl]
          · simp [hrk, hrs, hrl]
  have h := key (Finset.univ.erase l0) (Finset.notMem_erase l0 _)
  convert h using 2
  funext r
  by_cases hr : r = l0
  · subst hr
    rw [ite_eq_right (Finset.notMem_erase r _), ite_eq_left (rfl : r = r),
      Finset.prod_inv_distrib]
    exact eq_inv_of_mul_eq_one_left ((Finset.mul_prod_erase _ D (Finset.mem_univ r)).trans hD)
  · simp [hr]

/-- Matrices of determinant one preserve the zero set. -/
theorem preservesZeroSet_of_det_eq_one {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)}
    (hW : ∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    (i : ι) (l0 : Fin (n i)) (g : Matrix (Fin (n i)) (Fin (n i)) ℂ) (hg : g.det = 1) :
    PreservesZeroSet n W i g :=
  Matrix.diagonal_transvection_induction (PreservesZeroSet n W i) g
    (fun D hD => by
      rw [hg, Matrix.det_diagonal] at hD
      exact preservesZeroSet_diagonal_of_prod_eq_one hW i l0 D hD)
    (fun t => preservesZeroSet_transvection hW i t.hij t.c) (fun _ _ hA hB => hA.mul hB)

/-- Invertible matrices preserve the zero set. -/
theorem preservesZeroSet_of_isUnit {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)}
    (hW : ∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    (i : ι) (g : Matrix (Fin (n i)) (Fin (n i)) ℂ) (hg : IsUnit g.det) :
    PreservesZeroSet n W i g := by
  rcases Nat.eq_zero_or_pos (n i) with h0 | hpos
  · intro Y hY
    have hgY : g * Y i * g⁻¹ = Y i := by
      ext r q
      exact absurd r.isLt (by omega)
    rw [hgY, Function.update_eq_self]
    exact hY
  · obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq g.det hpos
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hpos.ne'] at hμ
      exact hg.ne_zero hμ.symm
    have h1 : (μ⁻¹ • g).det = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hμ, inv_mul_cancel₀ hg.ne_zero]
    have h := (preservesZeroSet_of_det_eq_one hW i ⟨0, hpos⟩ _ h1).smul
      (by rw [h1]; exact isUnit_one) hμ0
    rwa [smul_smul, mul_inv_cancel₀ hμ0, one_smul] at h

/-- The zero set of a stable space is invariant under blockwise conjugation by invertible
matrices. -/
theorem conj_mem_zeroSet {W : Submodule ℂ (MvPolynomial (Coord n) ℂ)}
    (hW : ∀ (i : ι) (a b : Fin (n i)), a ≠ b → ∀ f ∈ W, coadDer ℂ n (unit ℂ n i a b) f ∈ W)
    (g : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (hg : ∀ i, IsUnit (g i).det)
    {Y : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ} (hY : Y ∈ zeroSet n W) :
    (fun i => g i * Y i * (g i)⁻¹) ∈ zeroSet n W := by
  have key : ∀ s : Finset ι,
      (fun i => if i ∈ s then g i * Y i * (g i)⁻¹ else Y i) ∈ zeroSet n W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hY
    | insert j s hjs ih =>
      have h := preservesZeroSet_of_isUnit hW j (g j) (hg j) _ ih
      convert h using 1
      funext i
      by_cases hij : i = j
      · subst hij; simp [hjs]
      · simp [hij]
  simpa using key Finset.univ

end Invariance

/-- The regular nilpotent tuple with superdiagonal entries `c i p`. -/
def regularTuple (c : ∀ i, Fin (n i) → ℂ) : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ :=
  fun i => Matrix.of fun p q => if (q : ℕ) = p + 1 then c i p else 0

/-- Kostant's orbit statement: a stable space vanishing at the regular nilpotent tuple vanishes
on all nilpotent tuples. -/
theorem orbitVanishing : OrbitVanishingStatement n := by
  intro W hW c hc hψ f hf M hM
  have hψZ : regularTuple n c ∈ zeroSet n W := by
    intro g hg
    have hpt : tuplePoint n (regularTuple n c) =
        fun v : Coord n => if (v.2.2 : ℕ) = v.2.1 + 1 then c v.1 v.2.1 else 0 := by
      funext v
      rfl
    rw [hpt]
    exact hψ g hg
  -- Strictly upper triangular tuples with nonzero superdiagonal are in the zero set.
  have hreg : ∀ U : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ,
      (∀ (i : ι) (p q : Fin (n i)), q ≤ p → U i p q = 0) →
      (∀ (i : ι) (p q : Fin (n i)), (q : ℕ) = p + 1 → U i p q ≠ 0) → U ∈ zeroSet n W := by
    intro U hU hU'
    have hex : ∀ i, ∃ g : (Matrix (Fin (n i)) (Fin (n i)) ℂ)ˣ,
        (g : Matrix (Fin (n i)) (Fin (n i)) ℂ) * regularTuple n c i *
          (↑g⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ) = U i := fun i =>
      exists_conj_of_regular (regularTuple n c i) (U i)
        (fun p q hqp => by
          have := Fin.le_iff_val_le_val.mp hqp
          simp only [regularTuple, Matrix.of_apply]
          exact ite_eq_right (by omega))
        (fun p q hpq => by
          have := q.isLt
          simp only [regularTuple, Matrix.of_apply]
          rw [ite_eq_left hpq]
          exact hc i p (by omega))
        (hU i) (hU' i)
    choose g hg using hex
    have key : U = fun i => (g i : Matrix (Fin (n i)) (Fin (n i)) ℂ) * regularTuple n c i *
        (g i : Matrix (Fin (n i)) (Fin (n i)) ℂ)⁻¹ := by
      funext i
      rw [← hg i, Matrix.coe_units_inv]
    rw [key]
    exact conj_mem_zeroSet hW (fun i => (g i : Matrix (Fin (n i)) (Fin (n i)) ℂ))
      (fun i => (Matrix.isUnit_iff_isUnit_det _).mp (g i).isUnit) hψZ
  -- Density: all strictly upper triangular tuples are in the zero set.
  have hupper : ∀ U : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ,
      (∀ (i : ι) (p q : Fin (n i)), q ≤ p → U i p q = 0) → U ∈ zeroSet n W := by
    intro U hU g hg
    obtain ⟨F, hF⟩ : ∃ F : MvPolynomial (Coord n) ℂ,
        F = bind₁ (fun v : Coord n => if v.2.1 < v.2.2 then (X v : MvPolynomial (Coord n) ℂ)
          else 0) g := ⟨_, rfl⟩
    have hevalF : ∀ x : Coord n → ℂ,
        eval x F = eval (fun v : Coord n => if v.2.1 < v.2.2 then x v else 0) g := by
      intro x
      change aeval x F = aeval (fun v : Coord n => if v.2.1 < v.2.2 then x v else 0) g
      rw [hF, aeval_bind₁]
      refine congrArg (fun φ : Coord n → ℂ => aeval φ g) (funext fun v => ?_)
      by_cases h : v.2.1 < v.2.2 <;> simp [h]
    have hF0 : F = 0 := by
      refine MvPolynomial.funext_set
        (fun v : Coord n => if (v.2.2 : ℕ) = v.2.1 + 1 then ({0}ᶜ : Set ℂ) else Set.univ)
        (fun v => ?_) (fun x hx => ?_)
      · by_cases h : (v.2.2 : ℕ) = v.2.1 + 1
        · rw [ite_eq_left h]; exact (Set.finite_singleton 0).infinite_compl
        · rw [ite_eq_right h]; exact Set.infinite_univ
      · rw [map_zero, hevalF]
        refine hreg (fun i => Matrix.of fun p q => if p < q then x ⟨i, p, q⟩ else 0)
          (fun i p q hqp => by simp [not_lt.mpr hqp]) (fun i p q hpq => ?_) g hg
        have hlt : p < q := by rw [Fin.lt_def]; omega
        have hxv := hx ⟨i, p, q⟩ (Set.mem_univ _)
        simp only [hpq, ite_true, Set.mem_compl_iff, Set.mem_singleton_iff] at hxv
        simpa [hlt] using hxv
    have hFU : eval (tuplePoint n U) F = eval (tuplePoint n U) g := by
      rw [hevalF]
      refine congrArg (fun φ : Coord n → ℂ => eval φ g) (funext fun v => ?_)
      by_cases h : v.2.1 < v.2.2
      · simp [h]
      · simp only [h, ite_false, tuplePoint]
        exact (hU v.1 v.2.1 v.2.2 (not_lt.mp h)).symm
    rw [← hFU, hF0, map_zero]
  -- Every nilpotent tuple is conjugate to a strictly upper triangular one.
  have hnil : ∀ i, ∃ g : (Matrix (Fin (n i)) (Fin (n i)) ℂ)ˣ, ∀ p q : Fin (n i), q ≤ p →
      ((g : Matrix (Fin (n i)) (Fin (n i)) ℂ) * M i *
        (↑g⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ)) p q = 0 :=
    fun i => exists_conj_strictUpper (M i) (hM i)
  choose g hg using hnil
  have hUZ := hupper (fun i => (g i : Matrix (Fin (n i)) (Fin (n i)) ℂ) * M i *
    (↑(g i)⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ)) hg
  have key : M = fun i => (↑(g i)⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ) *
      ((g i : Matrix (Fin (n i)) (Fin (n i)) ℂ) * M i *
        (↑(g i)⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ)) *
      (↑(g i)⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ)⁻¹ := by
    funext i
    rw [← Matrix.coe_units_inv, inv_inv]
    simp only [mul_assoc, Units.inv_mul, mul_one]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  have hMZ : M ∈ zeroSet n W := by
    rw [key]
    exact conj_mem_zeroSet hW (fun i => (↑(g i)⁻¹ : Matrix (Fin (n i)) (Fin (n i)) ℂ))
      (fun i => (Matrix.isUnit_iff_isUnit_det _).mp (g i)⁻¹.isUnit) hUZ
  exact hMZ f hf

end Langlands.Archimedean.Kostant
