import Langlands.BaseChange.CyclicNormLemma
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # A coordinate polynomial for the σ-regular locus -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands _root_.Polynomial

private def matrixResultant {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : R :=
  M.charpoly.resultant M.charpoly.derivative n (n - 1)

private theorem matrixResultant_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    matrixResultant (M.map φ) = φ (matrixResultant M) := by
  unfold matrixResultant
  rw [Matrix.charpoly_map, derivative_map, resultant_map_map]

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] {n m : ℕ}

private theorem matrixResultant_ne_zero (M : Matrix (Fin n) (Fin n) F) :
    matrixResultant M ≠ 0 ↔ M.charpoly.Separable := by
  let p := M.charpoly
  have hmonic : p.Monic := Matrix.charpoly_monic _
  have hdeg : p.natDegree = n := by simp [p, Matrix.charpoly_natDegree_eq_dim]
  change p.resultant p.derivative n (n - 1) ≠ 0 ↔ p.Separable
  have hder : p.derivative.natDegree ≤ n - 1 := hdeg ▸ natDegree_derivative_le p
  have hresult : p.resultant p.derivative n (n - 1) = p.resultant p.derivative := calc
    _ = p.resultant p.derivative n (p.derivative.natDegree +
        (n - 1 - p.derivative.natDegree)) := by rw [Nat.add_sub_of_le hder]
    _ = _ := by
      rw [resultant_add_right_deg _ _ _ _ _ le_rfl, ← hdeg, coeff_natDegree,
        hmonic.leadingCoeff, one_pow, one_mul]
  rw [hresult, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hmonic, separable_def]

private theorem matrixResultant_of_associated {σ : E ≃ₐ[F] E} {l : ℕ}
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (h : IsNormAssociated σ l δ γ) :
    matrixResultant (cyclicNorm σ l δ : Matrix (Fin n) (Fin n) E) =
      algebraMap F E (matrixResultant (γ : Matrix (Fin n) (Fin n) F)) := by
  obtain ⟨g, hg⟩ := h
  have hp := congrArg (fun a : GeneralLinear n E =>
    (a : Matrix (Fin n) (Fin n) E).charpoly) hg
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj'] at hp
  calc
    _ = matrixResultant ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E)) := by
      unfold matrixResultant
      rw [hp]
      rfl
    _ = _ := matrixResultant_map _ _

private def genericMatrix (b : Module.Basis (Fin m) F (Matrix (Fin n) (Fin n) E))
    (τ : E ≃ₐ[F] E) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) E) :=
  Matrix.of fun i j => ∑ k, MvPolynomial.C (τ (b k i j)) * MvPolynomial.X k

private theorem eval_genericMatrix
    (b : Module.Basis (Fin m) F (Matrix (Fin n) (Fin n) E)) (τ : E ≃ₐ[F] E)
    (x : Fin m → F) :
    (genericMatrix b τ).map (MvPolynomial.eval (algebraMap F E ∘ x)) =
      (b.equivFun.symm x).map τ := by
  ext i j
  change MvPolynomial.eval (algebraMap F E ∘ x)
    (∑ k, MvPolynomial.C (τ (b k i j)) * MvPolynomial.X k) =
      τ (b.equivFun.symm x i j)
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Function.comp_apply, Module.Basis.equivFun_symm_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change τ (b k i j) * algebraMap F E (x k) = τ (x k • b k i j)
  rw [Algebra.smul_def, map_mul, τ.commutes, mul_comm]

private def symbolicProduct (b : Module.Basis (Fin m) F (Matrix (Fin n) (Fin n) E))
    (σ : E ≃ₐ[F] E) (l : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) E) :=
  ((List.range l).map fun i => genericMatrix b (σ ^ i)).prod

private theorem eval_symbolicProduct
    (b : Module.Basis (Fin m) F (Matrix (Fin n) (Fin n) E)) (σ : E ≃ₐ[F] E)
    (l : ℕ) (M : Matrix (Fin n) (Fin n) E) :
    (symbolicProduct b σ l).map (MvPolynomial.eval (algebraMap F E ∘ b.equivFun M)) =
      ((List.range l).map fun i => M.map (σ ^ i : E ≃ₐ[F] E)).prod := by
  change (MvPolynomial.eval (algebraMap F E ∘ b.equivFun M)).mapMatrix
    (((List.range l).map fun i => genericMatrix b (σ ^ i)).prod) = _
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  change (genericMatrix b (σ ^ i)).map (MvPolynomial.eval (algebraMap F E ∘ b.equivFun M)) =
    M.map (σ ^ i : E ≃ₐ[F] E)
  rw [eval_genericMatrix, LinearEquiv.symm_apply_apply]

private def projectCoeffs (r : E →ₗ[F] F) (p : MvPolynomial (Fin m) E) :
    MvPolynomial (Fin m) F :=
  ∑ d ∈ p.support, MvPolynomial.monomial d (r (p.coeff d))

private theorem eval_projectCoeffs (r : E →ₗ[F] F) (p : MvPolynomial (Fin m) E)
    (x : Fin m → F) :
    MvPolynomial.eval x (projectCoeffs r p) =
      r (MvPolynomial.eval (algebraMap F E ∘ x) p) := by
  unfold projectCoeffs
  rw [MvPolynomial.eval_sum, ← MvPolynomial.eval₂_id, MvPolynomial.eval₂_eq', map_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, RingHom.id_apply,
    Function.comp_apply]
  have hprod : algebraMap F E (∏ i, x i ^ d i) =
      ∏ i, (algebraMap F E (x i)) ^ d i := by
    simp only [map_prod, map_pow]
  rw [← hprod, mul_comm (p.coeff d), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

private theorem exists_distinct_powers [Infinite F] {l : ℕ} (hl : 0 < l) :
    ∃ a : Fin n → F, Function.Injective (fun i => a i ^ l) := by
  let f (x : F) := x ^ l
  have hinf : (Set.range f).Infinite := by
    intro hfinite
    have : Finite (Set.range f) := Set.finite_coe_iff.mpr hfinite
    let intoRange (x : F) : Set.range f := ⟨f x, Set.mem_range_self x⟩
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber intoRange
    let q : Polynomial F := X ^ l - C (y : F)
    have hq : q ≠ 0 := X_pow_sub_C_ne_zero hl (y : F)
    have hfiber : intoRange ⁻¹' {y} ⊆ {x | q.IsRoot x} := by
      intro x hx
      have hx' : intoRange x = y := Set.mem_singleton_iff.mp hx
      change (X ^ l - C (y : F)).eval x = 0
      rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
      exact congrArg Subtype.val hx'
    exact (q.finite_setOfPred_isRoot hq |>.subset hfiber).not_infinite
      (Set.infinite_coe_iff.mp hy)
  let t (i : Fin n) := Set.Infinite.natEmbedding _ hinf (i : ℕ)
  have ht : Function.Injective t :=
    (Set.Infinite.natEmbedding _ hinf).injective.comp Fin.val_injective
  choose a ha using fun i : Fin n => (t i).property
  refine ⟨a, fun i j hij => ht (Subtype.ext ?_)⟩
  rw [← ha i, ← ha j]
  exact hij

/-- A nonzero polynomial in any finite `F`-basis of the matrix algebra
detects the σ-regular elements on its unit group. -/
theorem exists_sigmaRegular_polynomial [Infinite F]
    {σ : E ≃ₐ[F] E} {l : ℕ} (hE : IsCyclicAlgebra σ l)
    (b : Module.Basis (Fin m) F (Matrix (Fin n) (Fin n) E)) :
    ∃ p : MvPolynomial (Fin m) F, p ≠ 0 ∧ ∀ δ : GeneralLinear n E,
      IsSigmaRegular σ l δ ↔
        MvPolynomial.eval (b.equivFun (δ : Matrix (Fin n) (Fin n) E)) p ≠ 0 := by
  have : Module.Finite F E := hE.1
  have : Nontrivial E := Module.finrank_pos_iff.mp (hE.2.1.symm ▸ hE.pos)
  obtain ⟨r, hr⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have hr' (x : F) : r (algebraMap F E x) = x := DFunLike.congr_fun hr x
  let p := projectCoeffs r (matrixResultant (symbolicProduct b σ l))
  have heval (M : Matrix (Fin n) (Fin n) E) :
      MvPolynomial.eval (b.equivFun M) p = r (matrixResultant
        (((List.range l).map fun i => M.map (σ ^ i : E ≃ₐ[F] E)).prod)) := by
    dsimp only [p]
    rw [eval_projectCoeffs, ← matrixResultant_map, eval_symbolicProduct]
  refine ⟨p, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_distinct_powers (F := F) (n := n) hE.pos
    let D := Matrix.diagonal a
    let M := D.map (algebraMap F E)
    have hfixed i : M.map (σ ^ i : E ≃ₐ[F] E) = M := by
      ext k j
      exact (σ ^ i).commutes (D k j)
    have hsep : (D ^ l).charpoly.Separable := by
      change ((Matrix.diagonal a) ^ l).charpoly.Separable
      rw [Matrix.diagonal_pow, Matrix.charpoly_diagonal]
      exact separable_prod_X_sub_C_iff.mpr ha
    have hprod (k : ℕ) : ((List.range k).map fun _ => M).prod = M ^ k := by
      induction k with
      | zero => simp
      | succ k ih => simp [List.range_succ, List.prod_append, pow_succ]
    have hval : MvPolynomial.eval (b.equivFun M) p = matrixResultant (D ^ l) := by
      rw [heval]
      simp only [hfixed, hprod]
      change r (matrixResultant ((algebraMap F E).mapMatrix D ^ l)) = _
      rw [← map_pow, RingHom.mapMatrix_apply, matrixResultant_map, hr']
    intro hp
    rw [hp, map_zero] at hval
    exact (matrixResultant_ne_zero _).mpr hsep hval.symm
  · intro δ
    have hval {γ : GeneralLinear n F} (hγ : IsNormAssociated σ l δ γ) :
        MvPolynomial.eval (b.equivFun (δ : Matrix (Fin n) (Fin n) E)) p =
          matrixResultant (γ : Matrix (Fin n) (Fin n) F) := by
      rw [heval]
      have hprod : ((List.range l).map fun i =>
          (δ : Matrix (Fin n) (Fin n) E).map (σ ^ i : E ≃ₐ[F] E)).prod =
          (cyclicNorm σ l δ : Matrix (Fin n) (Fin n) E) := by
        change _ = (Units.coeHom (Matrix (Fin n) (Fin n) E))
          (cyclicNorm σ l δ)
        simp only [cyclicNorm, map_list_prod, List.map_map]
        apply congrArg List.prod
        apply List.map_congr_left
        intro i _
        ext k j
        rfl
      rw [hprod, matrixResultant_of_associated hγ, hr']
    constructor
    · rintro ⟨γ, hγ, hreg⟩
      rw [hval hγ]
      exact (matrixResultant_ne_zero _).2 hreg
    · intro hp
      obtain ⟨γ, hγ⟩ := (cyclicNormLemma F E σ l n hE).1 δ
      refine ⟨γ, hγ, (matrixResultant_ne_zero _).1 ?_⟩
      exact hval hγ ▸ hp

end Langlands.BaseChange
