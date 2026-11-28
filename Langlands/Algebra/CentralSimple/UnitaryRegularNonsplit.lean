import Langlands.Algebra.CentralSimple.UnitaryRegularSplit
import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.Shimura.Unitary.HermitianAdjointChart
import Langlands.LinearAlgebra.HermitianDiagonalization

/-! # Regular unitary elements at a place not split in the quadratic extension -/

noncomputable section

universe u

open scoped TensorProduct
open Polynomial

namespace Langlands.CentralSimple.UnitaryPoints

section Polynomials

/-- The reflection of `∏ (X - uᵢ)` when `uᵢ σ(uᵢ) = 1`. -/
theorem reflect_prod_X_sub_C {R : Type*} [CommRing R] (σ : R →+* R) {ι : Type*}
    (s : Finset ι) (v : ι → R) (hv : ∀ i ∈ s, v i * σ (v i) = 1) :
    reflect s.card (∏ i ∈ s, (X - C (v i))) =
      C (∏ i ∈ s, -v i) * (∏ i ∈ s, (X - C (v i))).map σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdeg : (∏ i ∈ s, (X - C (v i))).natDegree ≤ s.card := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ i ∈ s, (X - C (v i)).natDegree ≤ ∑ _i ∈ s, (1 : ℕ) :=
            Finset.sum_le_sum (f := fun i => (X - C (v i)).natDegree)
              fun i _ => natDegree_X_sub_C_le (v i)
        _ = s.card := by simp
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm,
      reflect_mul _ _ (natDegree_X_sub_C_le (v a)) hdeg,
      ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)), reflect_sub, reflect_one_X,
      reflect_C, Finset.prod_insert ha, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
    have key : (1 : R[X]) - C (v a) * X ^ 1 = C (-v a) * (X - C (σ (v a))) := by
      rw [pow_one, mul_sub, ← C_mul, neg_mul, hv a (Finset.mem_insert_self a s)]
      simp only [C_neg, C_1]
      ring
    rw [key, C_mul]
    ring

/-- **Conjugate reciprocity.** If `uᵢ σ(uᵢ) = 1`, the coefficients of `f = ∏ (X - uᵢ)`
satisfy `f_{n-i} = (-1)ⁿ (∏ uᵢ) σ(f_i)`. -/
theorem coeff_prod_X_sub_C_reciprocal {R : Type*} [CommRing R] (σ : R →+* R) {n : ℕ}
    (v : Fin n → R) (hv : ∀ i, v i * σ (v i) = 1) (i : ℕ) (hi : i ≤ n) :
    (∏ j, (X - C (v j))).coeff (n - i) =
      (-1) ^ n * (∏ j, v j) * σ ((∏ j, (X - C (v j))).coeff i) := by
  have h := reflect_prod_X_sub_C σ Finset.univ v (fun j _ => hv j)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hc := congrArg (fun p => p.coeff i) h
  rw [coeff_reflect, revAt_le hi, coeff_C_mul, coeff_map] at hc
  rw [hc, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

end Polynomials

section NormOne

variable {L : Type*} [Field L] (N : Set L) (hN : N.Infinite)
  (hmul : ∀ a ∈ N, ∀ b ∈ N, a * b ∈ N) (hinv : ∀ a ∈ N, a⁻¹ ∈ N) (h0 : ∀ a ∈ N, a ≠ 0)
include hN hmul hinv h0

theorem exists_injective_prod_eq_add_two (n : ℕ) :
    ∀ (w : L), w ∈ N → ∀ T : Finset L, ∃ v : Fin (n + 2) → L, Function.Injective v ∧
      (∀ i, v i ∈ N ∧ v i ∉ T) ∧ ∏ i, v i = w := by
  classical
  induction n with
  | zero =>
    intro w hw T
    show ∃ v : Fin 2 → L, Function.Injective v ∧ (∀ i, v i ∈ N ∧ v i ∉ T) ∧ ∏ i, v i = w
    let bad : Finset L :=
      T ∪ T.image (fun t => w * t⁻¹) ∪ ((X : L[X]) ^ 2 - C w).roots.toFinset
    obtain ⟨a, haN, hab⟩ := hN.exists_notMem_finset bad
    have ha0 := h0 a haN
    have hw0 := h0 w hw
    simp only [bad, Finset.mem_union, Finset.mem_image, Multiset.mem_toFinset, not_or] at hab
    obtain ⟨⟨haT, hai⟩, har⟩ := hab
    have hsq : a ^ 2 ≠ w := by
      intro h
      apply har
      rw [mem_roots (X_pow_sub_C_ne_zero (by norm_num) w), IsRoot, eval_sub, eval_pow,
        eval_X, eval_C, h, sub_self]
    have hne : a ≠ w * a⁻¹ := by
      intro h
      apply hsq
      rw [pow_two]
      nth_rewrite 2 [h]
      field_simp
    refine ⟨![a, w * a⁻¹], ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    · intro i
      fin_cases i
      · exact ⟨haN, haT⟩
      · refine ⟨hmul w hw _ (hinv a haN), fun ht => hai ⟨w * a⁻¹, ht, ?_⟩⟩
        field_simp
    · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      field_simp
  | succ n ih =>
    intro w hw T
    obtain ⟨b, hbN, hbT⟩ := hN.exists_notMem_finset T
    obtain ⟨v, hvinj, hvN, hvprod⟩ := ih (w * b⁻¹) (hmul w hw _ (hinv b hbN)) (insert b T)
    refine ⟨Fin.cons b v, ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hvinj⟩
      rintro ⟨i, hi⟩
      exact (hvN i).2 (hi ▸ Finset.mem_insert_self _ _)
    · intro i
      refine Fin.cases ⟨hbN, hbT⟩ (fun j => ?_) i
      rw [Fin.cons_succ]
      exact ⟨(hvN j).1, fun h => (hvN j).2 (Finset.mem_insert_of_mem h)⟩
    · rw [Fin.prod_cons, hvprod]
      field_simp [h0 b hbN]

/-- In an infinite set of nonzero elements of a field closed under products and inverses,
every element is a product of `n ≥ 1` distinct elements. -/
theorem exists_injective_prod_eq (n : ℕ) (hn : 0 < n) (w : L) (hw : w ∈ N) :
    ∃ v : Fin n → L, Function.Injective v ∧ (∀ i, v i ∈ N) ∧ ∏ i, v i = w := by
  obtain _ | _ | m := n
  · exact absurd hn (lt_irrefl 0)
  · exact ⟨fun _ => w, fun i j _ => Fin.ext (by have := i.2; have := j.2; omega),
      fun _ => hw, by simp⟩
  · obtain ⟨v, hv, hvN, hvp⟩ := exists_injective_prod_eq_add_two N hN hmul hinv h0 m w hw ∅
    exact ⟨v, hv, fun i => (hvN i).1, hvp⟩

end NormOne

section Matrix

open Langlands.Shimura Langlands.Shimura.FiniteUnitary

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] {n : ℕ}

/-- The ring endomorphism underlying an involution of a field. -/
def involutionRingHom (c : AlgebraInvolution R L) : L →+* L where
  toFun := c
  map_one' := c.apply_one
  map_mul' a b := by rw [c.apply_mul, mul_comm]
  map_zero' := c.apply_zero
  map_add' := c.apply_add

/-- Let `ρ` be an involution of `M_n(L)` acting on the scalars by a nontrivial involution `c`
of `L` with `2 ≠ 0`. There is an invertible `Q` such that `Q diag(v) Q⁻¹` is unitary for `ρ`
whenever `vᵢ c(vᵢ) = 1` for all `i`. -/
theorem exists_unitary_conj_diagonal (hn : 0 < n) (c : AlgebraInvolution R L)
    (hc : ∃ a : L, c a ≠ a) (h2 : (2 : L) ≠ 0)
    (ρ : AlgebraInvolution R (Matrix (Fin n) (Fin n) L))
    (hρ : ∀ a : L, ρ (algebraMap L _ a) = algebraMap L _ (c a)) :
    ∃ Q : (Matrix (Fin n) (Fin n) L)ˣ, ∀ v : Fin n → L, (∀ i, v i * c (v i) = 1) →
      ((Q : Matrix (Fin n) (Fin n) L) * Matrix.diagonal v * (Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ)) *
        ρ ((Q : Matrix (Fin n) (Fin n) L) * Matrix.diagonal v *
          (Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ)) = 1 := by
  classical
  set θ := matrixTranspose c n
  obtain ⟨H, hH, hρH⟩ := exists_hermitianGram_of_matrixInvolution c hn hc ρ hρ
  let c' := involutionRingHom c
  set G : Matrix (Fin n) (Fin n) L := (H : Matrix (Fin n) (Fin n) L) with hGdef
  have hG : ∀ a b, c' (G a b) = G b a := by
    intro a b
    have := congrFun (congrFun hH b) a
    rw [matrixTranspose_apply] at this
    exact this
  obtain ⟨P, d, hP, hPd, -, -⟩ :=
    Langlands.Sesquilinear.exists_congr_diagonal_of_hermitian (c := c') h2
      (fun t => c.apply_apply t) hG
  have hQdet : IsUnit (P.map c').det := by
    have h : (P.map c').det = c' P.det := (RingHom.map_det c' P).symm
    rw [h]
    exact isUnit_iff_ne_zero.mpr ((_root_.map_ne_zero c').mpr hP)
  let Q : (Matrix (Fin n) (Fin n) L)ˣ := ((Matrix.isUnit_iff_isUnit_det _).mpr hQdet).unit
  set Qm : Matrix (Fin n) (Fin n) L := (Q : Matrix (Fin n) (Fin n) L) with hQm
  set Qi : Matrix (Fin n) (Fin n) L := ((Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ) :
    Matrix (Fin n) (Fin n) L) with hQi
  have hQ : Qm = P.map c' := rfl
  have hθQ : θ Qm = P.transpose := by
    ext i j
    rw [matrixTranspose_apply, hQ, Matrix.map_apply, Matrix.transpose_apply]
    exact c.apply_apply _
  have hD : θ Qm * (G * Qm) = Matrix.diagonal d := by
    rw [hθQ, ← Matrix.mul_assoc, hQ]
    exact hPd
  have hinv : θ Qi * θ Qm = 1 := by
    rw [← θ.apply_mul, hQi, hQm, Units.mul_inv, θ.apply_one]
  have hQQ : Qm * Qi = 1 := Units.mul_inv Q
  refine ⟨Q, fun v hv => ?_⟩
  have hθΔ : θ (Matrix.diagonal v) = Matrix.diagonal (fun i => c (v i)) := by
    ext i j
    rw [matrixTranspose_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.diagonal_apply_ne _ hij, c.apply_zero]
  have hΔ : θ (Matrix.diagonal v) * (Matrix.diagonal d * Matrix.diagonal v) =
      Matrix.diagonal d := by
    rw [hθΔ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_comm (d i), ← mul_assoc, mul_comm (c (v i)), hv i, one_mul]
  change (Qm * Matrix.diagonal v * Qi) * ρ (Qm * Matrix.diagonal v * Qi) = 1
  set X := Qm * Matrix.diagonal v * Qi with hX
  have hθX : θ X * G * X = G := by
    rw [hX, θ.apply_mul, θ.apply_mul]
    calc θ Qi * (θ (Matrix.diagonal v) * θ Qm) * G * (Qm * Matrix.diagonal v * Qi)
        = θ Qi * (θ (Matrix.diagonal v) * ((θ Qm * (G * Qm)) * Matrix.diagonal v)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = θ Qi * (θ Qm * (G * Qm)) * Qi := by
          rw [hD, hΔ]
      _ = (θ Qi * θ Qm) * G * (Qm * Qi) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hinv, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hleft : ρ X * X = 1 := by
    rw [hρH, AlgebraInvolution.adjoint_apply, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (θ X), ← hGdef, hθX, hGdef, Units.inv_mul]
  exact mul_eq_one_comm.mp hleft

/-- A polynomial evaluated at a diagonal matrix is the diagonal matrix of its values. -/
theorem aeval_diagonal (v : Fin n → L) (p : L[X]) :
    aeval (Matrix.diagonal v) p = Matrix.diagonal (fun j => p.eval (v j)) := by
  have h := aeval_algHom_apply
    (Matrix.diagonalAlgHom L : (Fin n → L) →ₐ[L] Matrix (Fin n) (Fin n) L) v p
  rw [Matrix.diagonalAlgHom_apply, Matrix.diagonalAlgHom_apply] at h
  rw [h]
  congr 1
  funext j
  rw [show (aeval v p) j = Pi.evalAlgHom L (fun _ => L) j (aeval v p) from rfl,
    ← aeval_algHom_apply, Pi.evalAlgHom_apply, coe_aeval_eq_eval]

/-- Conjugation by a unit of `M_n(L)` as an `L`-algebra homomorphism. -/
def conjAlgHom (Q : (Matrix (Fin n) (Fin n) L)ˣ) :
    Matrix (Fin n) (Fin n) L →ₐ[L] Matrix (Fin n) (Fin n) L where
  toFun Y := (Q : Matrix (Fin n) (Fin n) L) * Y * (Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ)
  map_one' := by rw [Matrix.mul_one, Units.mul_inv]
  map_mul' Y Y' := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ)) : Matrix (Fin n) (Fin n) L)
      (Q : Matrix (Fin n) (Fin n) L), Units.inv_mul, Matrix.one_mul]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' Y Y' := by rw [Matrix.mul_add, Matrix.add_mul]
  commutes' a := by
    rw [← Algebra.commutes, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem conjAlgHom_apply (Q : (Matrix (Fin n) (Fin n) L)ˣ) (Y : Matrix (Fin n) (Fin n) L) :
    conjAlgHom Q Y =
      (Q : Matrix (Fin n) (Fin n) L) * Y * (Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ) := rfl

theorem conjAlgHom_injective (Q : (Matrix (Fin n) (Fin n) L)ˣ) :
    Function.Injective (conjAlgHom Q) := by
  intro Y Y' h
  have h' := congrArg (fun M => ((Q⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ) : Matrix (Fin n) (Fin n) L) *
    M * (Q : Matrix (Fin n) (Fin n) L)) h
  simp only [conjAlgHom_apply, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h'
  simpa only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] using h'

end Matrix

section Nonsplit

open Langlands.GroupScheme Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open Langlands.Shimura Langlands.Shimura.FiniteUnitary

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
/-- The scalars of `(E ⊗[F] K) ⊗[E] B` are the image of `ψ` under the identification
`tensorEquiv`, after `e ⊗ k ↦ k ⊗ e`. -/
theorem algebraMap_eq_tensorEquiv_centerMap (K : Type u) [CommRing K] [Algebra F K]
    (ℓ : E ⊗[F] K) :
    algebraMap (E ⊗[F] K) ((E ⊗[F] K) ⊗[E] B) ℓ =
      tensorEquiv F E B K (centerMap F E B K (Algebra.TensorProduct.comm F E K ℓ)) := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul e k =>
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      IsScalarTower.coe_toAlgHom', tensorEquiv_tmul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := B) e,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, hℓ, hℓ', map_add, map_add, map_add]

theorem centerConj_comm (K : Type u) [CommRing K] [Algebra F K] (ℓ : E ⊗[F] K) :
    centerConj F E K (Algebra.TensorProduct.comm F E K ℓ) =
      Algebra.TensorProduct.comm F E K
        (Algebra.TensorProduct.map (conjugation F E).toAlgHom (AlgHom.id F K) ℓ) := by
  induction ℓ using TensorProduct.inductionOn with
  | tmul e k => rfl
  | add ℓ ℓ' hℓ hℓ' => rw [map_add, map_add, hℓ, hℓ', map_add, map_add]

variable [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))
include hτ

/-- **Regular unitary elements at a place not split in `E`.** Let `K` be a field of
characteristic zero over which central simple algebras with unitary involutions split, with
`E ⊗[F] K` a field. If `z ⊗ 1` is the relative reduced norm of a unitary point of
`K ⊗[F] B`, there are a unitary `x ∈ K ⊗[F] B` and a monic conjugate-reciprocal `f` of
degree `n` over `K ⊗[F] E` with `f(x) = 0`, `f'(x)` a unit and `1, x, …, x^{n-1}`
independent over `K ⊗[F] E`. -/
theorem exists_regular_unitary_of_isField (K : Type u) [Field K] [CharZero K] [Algebra F K]
    (hK : UnitaryInvolutionSplitting K) (hfield : IsField (E ⊗[F] K))
    (n : ℕ) (hn : Module.finrank E B = n ^ 2) (z : Eˣ)
    (x₀ : (K ⊗[F] B)ˣ) (hx₀ : x₀ ∈ unitaryPoints τ K)
    (hz : (relativeNorm F E B K x₀ : E ⊗[F] K) = (z : E) ⊗ₜ[F] (1 : K)) :
    ∃ (x : K ⊗[F] B) (f : (K ⊗[F] E)[X]),
      x * τ.baseChange K x = 1 ∧ f.Monic ∧ f.natDegree = n ∧
      (∀ i ≤ n, f.coeff (n - i) = (-1) ^ n * ((1 : K) ⊗ₜ[F] (z : E)) *
          Algebra.TensorProduct.map (AlgHom.id K K) (conjugation F E).toAlgHom (f.coeff i)) ∧
      f.eval₂ (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F E B) :
          K ⊗[F] E →+* K ⊗[F] B) x = 0 ∧
      IsUnit ((derivative f).eval₂ (Algebra.TensorProduct.map (AlgHom.id K K)
          (IsScalarTower.toAlgHom F E B) : K ⊗[F] E →+* K ⊗[F] B) x) ∧
      ∀ c : Fin n → K ⊗[F] E,
        ∑ i, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F E B) (c i) *
          x ^ (i : ℕ) = 0 → c = 0 := by
  classical
  have hzz := mul_conjugation_eq_one τ hτ (z : E) x₀ hx₀ hz
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have hpos := Module.finrank_pos (R := E) (M := B)
      rw [hn, h] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  let : Field (E ⊗[F] K) := hfield.toField
  let : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  have hfin : Module.finrank K (E ⊗[F] K) = 2 := by
    rw [← (Algebra.TensorProduct.commRight F K E).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two F E]
  have : FiniteDimensional K (E ⊗[F] K) := .of_finrank_pos (by rw [hfin]; decide)
  have : Algebra.IsQuadraticExtension K (E ⊗[F] K) := { finrank_eq_two' := hfin }
  -- the conjugation of `E ⊗[F] K`
  let σ : (E ⊗[F] K) ≃ₐ[K] (E ⊗[F] K) := (Algebra.TensorProduct.commRight F K E).symm.trans
    ((tensorConjugation F E K).trans (Algebra.TensorProduct.commRight F K E))
  have hσ (ℓ : E ⊗[F] K) :
      σ ℓ = Algebra.TensorProduct.map (conjugation F E).toAlgHom (AlgHom.id F K) ℓ := by
    induction ℓ using TensorProduct.inductionOn with
    | tmul e k => rfl
    | add ℓ ℓ' h h' => rw [map_add, map_add, h, h']
  have hσσ (ℓ : E ⊗[F] K) : σ (σ ℓ) = ℓ := by
    induction ℓ using TensorProduct.inductionOn with
    | tmul e k =>
      rw [hσ, hσ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact congrArg (· ⊗ₜ[F] _) (conjugation_involutive F E e)
    | add ℓ ℓ' h h' => rw [map_add, map_add, h, h']
  have hinjE : Function.Injective (fun e : E => e ⊗ₜ[F] (1 : K)) :=
    (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] K).toRingHom.injective
  obtain ⟨ω, hω⟩ : ∃ ω : E, conjugation F E ω ≠ ω := by
    by_contra! h
    exact conjugation_ne_one F E (AlgEquiv.ext h)
  have hσω : σ (ω ⊗ₜ[F] (1 : K)) ≠ ω ⊗ₜ[F] (1 : K) := by
    intro h
    apply hω
    apply hinjE
    simpa only [hσ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
      using h
  have hσne : σ ≠ 1 := fun h => hσω (by rw [h]; rfl)
  -- the algebra `(E ⊗[F] K) ⊗[E] B` and its involution
  have : IsSimpleRing ((E ⊗[F] K) ⊗[E] B) := isSimpleRing_baseChange E B (E ⊗[F] K)
  have : Algebra.IsCentral (E ⊗[F] K) ((E ⊗[F] K) ⊗[E] B) :=
    isCentral_baseChange E B (E ⊗[F] K)
  let tE := tensorEquiv F E B K
  let τ' : (E ⊗[F] K) ⊗[E] B → (E ⊗[F] K) ⊗[E] B :=
    fun w => tE (τ.baseChange K (tE.symm w))
  have hτ'alg (ℓ : E ⊗[F] K) :
      τ' (algebraMap _ ((E ⊗[F] K) ⊗[E] B) ℓ) = algebraMap _ ((E ⊗[F] K) ⊗[E] B) (σ ℓ) := by
    change tE (τ.baseChange K (tE.symm _)) = _
    rw [algebraMap_eq_tensorEquiv_centerMap, AlgEquiv.symm_apply_apply,
      baseChange_centerMap K τ hτ, centerConj_comm, algebraMap_eq_tensorEquiv_centerMap, hσ]
  have hτ'inv : IsUnitaryInvolution (⇑σ) τ' := by
    refine ⟨fun a b => ?_, fun a b => ?_, fun a => ?_, hτ'alg⟩
    · simp only [τ', map_add]
    · simp only [τ', map_mul, FirstKindInvolution.map_mul]
    · simp only [τ', AlgEquiv.symm_apply_apply, FirstKindInvolution.apply_apply,
        AlgEquiv.apply_symm_apply]
  obtain ⟨m, ⟨Φ⟩⟩ := hK (E ⊗[F] K) σ hσne ((E ⊗[F] K) ⊗[E] B) τ' hτ'inv
  have hmn : n = m := by
    have h1 := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, hn, Module.finrank_matrix, Module.finrank_self,
      Fintype.card_fin, mul_one, ← sq] at h1
    exact Nat.pow_left_injective two_ne_zero h1
  subst hmn
  -- the involutions of `E ⊗[F] K` and of the matrix algebra
  let c : AlgebraInvolution ℤ (E ⊗[F] K) :=
    { linear := σ.toRingEquiv.toAddMonoidHom.toIntLinearMap
      map_one := map_one σ
      map_mul := fun a b => by
        change σ (a * b) = σ b * σ a
        rw [map_mul, mul_comm]
      involutive := hσσ }
  have hc (ℓ : E ⊗[F] K) : c ℓ = σ ℓ := rfl
  let ρf : Matrix (Fin n) (Fin n) (E ⊗[F] K) → Matrix (Fin n) (Fin n) (E ⊗[F] K) :=
    fun X => Φ (τ' (Φ.symm X))
  let ρ : AlgebraInvolution ℤ (Matrix (Fin n) (Fin n) (E ⊗[F] K)) :=
    { linear := (AddMonoidHom.mk' ρf (fun X Y => by
        simp only [ρf, map_add, hτ'inv.1, map_add])).toIntLinearMap
      map_one := by
        change Φ (τ' (Φ.symm 1)) = 1
        simp only [τ', map_one, FirstKindInvolution.map_one]
      map_mul := fun X Y => by
        change Φ (τ' (Φ.symm (X * Y))) = Φ (τ' (Φ.symm Y)) * Φ (τ' (Φ.symm X))
        rw [map_mul, hτ'inv.2.1, map_mul]
      involutive := fun X => by
        change Φ (τ' (Φ.symm (Φ (τ' (Φ.symm X))))) = X
        rw [AlgEquiv.symm_apply_apply, hτ'inv.2.2.1, AlgEquiv.apply_symm_apply] }
  have hρ (X : Matrix (Fin n) (Fin n) (E ⊗[F] K)) : ρ X = Φ (τ' (Φ.symm X)) := rfl
  have hρalg (a : E ⊗[F] K) : ρ (algebraMap _ _ a) = algebraMap _ _ (c a) := by
    rw [hρ, AlgEquiv.commutes, hτ'alg, AlgEquiv.commutes, hc]
  have : CharZero (E ⊗[F] K) :=
    charZero_of_injective_algebraMap (algebraMap K (E ⊗[F] K)).injective
  obtain ⟨Q, hQ⟩ := exists_unitary_conj_diagonal hn0 c
    ⟨ω ⊗ₜ[F] (1 : K), by rw [hc]; exact hσω⟩ two_ne_zero ρ hρalg
  -- distinct norm-one eigenvalues with product `z`
  let Nset : Set (E ⊗[F] K) := {v | v * σ v = 1}
  have hmul : ∀ a ∈ Nset, ∀ b ∈ Nset, a * b ∈ Nset := by
    intro a ha b hb
    change a * b * σ (a * b) = 1
    rw [map_mul, show a * b * (σ a * σ b) = (a * σ a) * (b * σ b) by ring, ha, hb, one_mul]
  have hinv : ∀ a ∈ Nset, a⁻¹ ∈ Nset := by
    intro a ha
    change a⁻¹ * σ a⁻¹ = 1
    rw [map_inv₀, ← mul_inv, ha, inv_one]
  have h0 : ∀ a ∈ Nset, a ≠ 0 := by
    intro a ha h
    change a * σ a = 1 at ha
    rw [h, zero_mul] at ha
    exact zero_ne_one ha
  have hNinf : Nset.Infinite := by
    have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    set ω' : E ⊗[F] K := ω ⊗ₜ[F] (1 : K)
    have hfix (t : K) : σ (algebraMap K _ t) = algebraMap K _ t := σ.commutes t
    have hden (t : K) : σ ω' + algebraMap K _ t ≠ 0 := by
      intro h
      apply hσω
      have h' := congrArg σ h
      rw [map_add, hσσ, hfix, map_zero] at h'
      exact (eq_neg_of_add_eq_zero_left h).trans (eq_neg_of_add_eq_zero_left h').symm
    have hnum (t : K) : ω' + algebraMap K _ t ≠ 0 := by
      intro h
      apply hσω
      have h' := congrArg σ h
      rw [map_add, hfix, map_zero] at h'
      exact (eq_neg_of_add_eq_zero_left h').trans (eq_neg_of_add_eq_zero_left h).symm
    let g : K → E ⊗[F] K := fun t => (ω' + algebraMap K _ t) / (σ ω' + algebraMap K _ t)
    refine Set.infinite_of_injective_forall_mem (f := g) ?_ ?_
    · intro s t hst
      simp only [g] at hst
      rw [div_eq_div_iff (hden s) (hden t)] at hst
      have hk : (algebraMap K (E ⊗[F] K) s - algebraMap K _ t) * (σ ω' - ω') = 0 := by
        linear_combination hst
      rcases mul_eq_zero.mp hk with h | h
      · exact (algebraMap K (E ⊗[F] K)).injective (sub_eq_zero.mp h)
      · exact absurd (sub_eq_zero.mp h) hσω
    · intro t
      change g t * σ (g t) = 1
      simp only [g, map_div₀, map_add, hσσ, hfix]
      rw [div_mul_div_comm, mul_comm (ω' + algebraMap K _ t),
        div_self (mul_ne_zero (hden t) (hnum t))]
  have hw : ((z : E) ⊗ₜ[F] (1 : K)) ∈ Nset := by
    change _ * σ _ = 1
    rw [hσ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    change ((z : E) * conjugation F E z) ⊗ₜ[F] (1 : K) = 1
    rw [hzz]
    rfl
  obtain ⟨v, hvinj, hvN, hvprod⟩ := exists_injective_prod_eq Nset hNinf hmul hinv h0 n hn0 _ hw
  -- the unitary element and the polynomial
  have hXu := hQ v (fun i => hvN i)
  set Xm : Matrix (Fin n) (Fin n) (E ⊗[F] K) := conjAlgHom Q (Matrix.diagonal v) with hXm
  let x' := Φ.symm Xm
  let κ : E ⊗[F] K →+* K ⊗[F] E :=
    ((Algebra.TensorProduct.comm F E K : E ⊗[F] K →ₐ[F] K ⊗[F] E) : E ⊗[F] K →+* K ⊗[F] E)
  let f' : (E ⊗[F] K)[X] := ∏ i, (X - C (v i))
  have hψκ : (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B).comp κ =
      (tE.symm : (E ⊗[F] K) ⊗[E] B →+* K ⊗[F] B).comp
        (algebraMap (E ⊗[F] K) ((E ⊗[F] K) ⊗[E] B)) := by
    refine RingHom.ext fun ℓ => ?_
    change centerMap F E B K (Algebra.TensorProduct.comm F E K ℓ) = tE.symm (algebraMap _ _ ℓ)
    rw [algebraMap_eq_tensorEquiv_centerMap, AlgEquiv.symm_apply_apply]
  have heval (p : (E ⊗[F] K)[X]) :
      (p.map κ).eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) (tE.symm x') =
        tE.symm (Φ.symm (conjAlgHom Q (aeval (Matrix.diagonal v) p))) := by
    rw [← aeval_algHom_apply (conjAlgHom Q), ← hXm, ← aeval_algHom_apply Φ.symm, aeval_def]
    change _ = (tE.symm : (E ⊗[F] K) ⊗[E] B →+* K ⊗[F] B) _
    rw [hom_eval₂, ← hψκ, eval₂_map]
    rfl
  have hdiag : aeval (Matrix.diagonal v) f' = 0 := by
    have h : (fun j => f'.eval (v j)) = 0 := by
      funext j
      simp only [f', eval_prod, eval_sub, eval_X, eval_C, Pi.zero_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
    rw [aeval_diagonal, h]
    exact Matrix.diagonal_zero
  refine ⟨tE.symm x', f'.map κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- unitarity
    have h1 : Φ (x' * τ' x') = 1 := by
      rw [map_mul]
      change Φ (Φ.symm Xm) * Φ (τ' (Φ.symm Xm)) = 1
      rw [AlgEquiv.apply_symm_apply]
      exact hXu
    have h2 : x' * τ' x' = 1 := by
      have h := congrArg Φ.symm h1
      rwa [AlgEquiv.symm_apply_apply, map_one] at h
    apply tE.injective
    rw [map_mul, map_one]
    rw [AlgEquiv.apply_symm_apply]
    exact h2
  · exact (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (v i)).map κ
  · rw [natDegree_map_eq_of_injective
      (show Function.Injective κ from (Algebra.TensorProduct.comm F E K).injective),
      natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  · -- conjugate reciprocity
    intro i hi
    rw [coeff_map, coeff_map,
      coeff_prod_X_sub_C_reciprocal (σ : E ⊗[F] K →+* E ⊗[F] K) v (fun j => hvN j) i hi,
      hvprod, map_mul, map_mul, map_pow, map_neg, map_one]
    congr 1
    change Algebra.TensorProduct.comm F E K (σ (f'.coeff i)) =
      centerConj F E K (Algebra.TensorProduct.comm F E K (f'.coeff i))
    rw [hσ, centerConj_comm]
  · -- `f(x) = 0`
    rw [heval, hdiag, map_zero, map_zero, map_zero]
  · -- `f'(x)` is a unit
    have hsep : f'.Separable := separable_prod_X_sub_C_iff'.mpr fun i _ j _ h => hvinj h
    rw [derivative_map, heval]
    exact (((isUnit_aeval_derivative_of_separable hsep hdiag).map (conjAlgHom Q)).map
      Φ.symm).map tE.symm
  · -- independence of the powers
    intro cc hcc
    let ℓ : Fin n → E ⊗[F] K := fun i => (Algebra.TensorProduct.comm F E K).symm (cc i)
    let p : (E ⊗[F] K)[X] := ∑ i : Fin n, C (ℓ i) * X ^ (i : ℕ)
    have hp : (p.map κ).eval₂ (centerMap F E B K : K ⊗[F] E →+* K ⊗[F] B) (tE.symm x') =
        ∑ i, centerMap F E B K (cc i) * (tE.symm x') ^ (i : ℕ) := by
      simp only [p, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        eval₂_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [C_mul_X_pow_eq_monomial, eval₂_monomial]
      have hκ : κ (ℓ i) = cc i := (Algebra.TensorProduct.comm F E K).apply_symm_apply (cc i)
      rw [hκ]
      rfl
    rw [← hp, heval] at hcc
    have h1 : aeval (Matrix.diagonal v) p = 0 := by
      apply conjAlgHom_injective Q
      rw [map_zero]
      apply Φ.symm.injective
      rw [map_zero]
      apply tE.symm.injective
      rw [map_zero]
      exact hcc
    rw [aeval_diagonal] at h1
    have h2 : ∀ j, p.eval (v j) = 0 := fun j => by
      simpa using congrFun (congrFun h1 j) j
    have hdeg : p.natDegree < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      by_cases hp0 : p = 0
      · rw [hp0, natDegree_zero]
        exact hn0
      · exact (natDegree_lt_iff_degree_lt hp0).mpr (degree_sum_fin_lt ℓ)
    have hp0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hvinj h2 hdeg
    funext i
    have hcoef : p.coeff i = ℓ i := by
      simp only [p, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [hp0, coeff_zero] at hcoef
    have hci : cc i = Algebra.TensorProduct.comm F E K (ℓ i) :=
      ((Algebra.TensorProduct.comm F E K).apply_symm_apply (cc i)).symm
    rw [hci, ← hcoef, map_zero]
    rfl

end Nonsplit

end Langlands.CentralSimple.UnitaryPoints
