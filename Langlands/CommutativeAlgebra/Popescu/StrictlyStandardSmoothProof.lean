import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardSmoothStatement
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Smooth.Basic

/-! # Proof: inverting a strictly standard element gives a smooth algebra -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

namespace StrictlyStandardSmooth

/-- First-order Taylor expansion for a square-zero perturbation. -/
theorem aeval_add_of_mul_eq_zero {R T σ : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Fintype σ] [DecidableEq σ] (t δ : σ → T) (hδ : ∀ i j, δ i * δ j = 0)
    (p : MvPolynomial σ R) :
    aeval (t + δ) p = aeval t p + ∑ i, aeval t (pderiv i p) * δ i := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p v hp =>
    have hsum : ∑ i, aeval t (pderiv i (p * X v)) * δ i =
        (∑ i, aeval t (pderiv i p) * δ i) * t v + aeval t p * δ v := by
      have h : ∀ i, pderiv i (p * X v) = pderiv i p * X v + p * pderiv i (X v) := fun i => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      simp only [h, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · rw [Finset.sum_eq_single v]
        · rw [pderiv_X_self, map_one, mul_one]
        · intro i _ hi
          rw [pderiv_X_of_ne (Ne.symm hi), map_zero, mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ v) h
    have h1 : (∑ i, aeval t (pderiv i p) * δ i) * δ v = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hδ, mul_zero]
    rw [map_mul, map_mul, aeval_X, aeval_X, hp, hsum, Pi.add_apply]
    linear_combination h1

/-- A `c × n` matrix whose maximal minors generate the unit ideal has a right inverse. -/
theorem exists_right_inverse {S : Type*} [CommRing S] {c n : ℕ} (M : Matrix (Fin c) (Fin n) S)
    (w : (Fin c ↪o Fin n) →₀ S) (hw : (w.sum fun e r => r * (M.submatrix id e).det) = 1) :
    ∃ N : Matrix (Fin n) (Fin c) S, M * N = 1 := by
  classical
  let P : (Fin c ↪o Fin n) → Matrix (Fin n) (Fin c) S :=
    fun e => Matrix.of fun i k => if i = e k then 1 else 0
  have hMP : ∀ e, M * P e = M.submatrix id e := by
    intro e
    ext j k
    simp [P, Matrix.mul_apply, Finset.sum_ite_eq']
  refine ⟨w.sum fun e r => r • (P e * (M.submatrix id e).adjugate), ?_⟩
  rw [Finsupp.sum, Matrix.mul_sum]
  simp_rw [Matrix.mul_smul, ← Matrix.mul_assoc, hMP, Matrix.mul_adjugate, smul_smul]
  rw [← Finset.sum_smul]
  rw [Finsupp.sum] at hw
  rw [hw, one_smul]

/-- The right inverse for the Jacobian matrix modulo `J`, from `a ∈ (Δ_e)` and `a` a unit. -/
theorem exists_right_inverse_of_mem_span {A S : Type*} [CommRing A] [CommRing S] {c n : ℕ}
    (κ : A →+* S) (M : Matrix (Fin c) (Fin n) S) (D : (Fin c ↪o Fin n) → A)
    (hD : ∀ e, κ (D e) = (M.submatrix id e).det) {a : A} (ha : a ∈ Ideal.span (Set.range D))
    {u : S} (hu : u * κ a = 1) : ∃ N : Matrix (Fin n) (Fin c) S, M * N = 1 := by
  classical
  obtain ⟨w, hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp ha
  refine exists_right_inverse M (w.mapRange (fun r => u * κ r) (by simp)) ?_
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp_rw [← hD]
  have : (w.sum fun e r => u * κ r * κ (D e)) = u * κ (w.sum fun e r => r • D e) := by
    rw [Finsupp.sum, Finsupp.sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [smul_eq_mul, map_mul, mul_assoc]
  rw [this, hw, hu]

end StrictlyStandardSmooth

open StrictlyStandardSmooth in
/-- Stacks Lemma 3.7(d) (07EZ): inverting a strictly standard element gives a smooth algebra. -/
theorem strictlyStandardSmooth : StrictlyStandardSmoothStatement.{u} := by
  intro R A _ _ _ a ha
  obtain ⟨n, m, c, hcn, hcm, f, φ, hφ, hker, hmem, g, hg, hgf⟩ := ha
  classical
  have : Algebra.FinitePresentation R A :=
    ⟨n, φ, hφ, by
      show (RingHom.ker φ).FG
      rw [hker]; exact Submodule.fg_span (Set.finite_range f)⟩
  have : Algebra.FinitePresentation A (Localization.Away a) :=
    IsLocalization.Away.finitePresentation a
  have : Algebra.FinitePresentation R (Localization.Away a) :=
    Algebra.FinitePresentation.trans R A _
  refine ⟨?_, inferInstance⟩
  apply Algebra.FormallySmooth.of_comp_surjective
  intro T _ _ J hJ ψ
  set Aa := Localization.Away a
  let θ : A →ₐ[R] T ⧸ J := ψ.comp (IsScalarTower.toAlgHom R A Aa)
  choose t ht using fun i : Fin n => Ideal.Quotient.mk_surjective (θ (φ (X i)))
  have hev : ∀ p, Ideal.Quotient.mk J (aeval t p) = θ (φ p) := by
    have h : (Ideal.Quotient.mkₐ R J).comp (aeval t) = θ.comp φ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [ht]
    intro p
    exact AlgHom.congr_fun h p
  have hfJ : ∀ j, aeval t (f j) ∈ J := fun j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hev]
    have h : f j ∈ RingHom.ker φ := by rw [hker]; exact Ideal.subset_span ⟨j, rfl⟩
    rw [show φ (f j) = 0 from h, map_zero]
  have hJsq : ∀ x ∈ J, ∀ y ∈ J, x * y = 0 := fun x hx y hy => by
    have h : x * y ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hJ] at h
    exact (Submodule.mem_bot _).mp h
  -- the inverse of `a` modulo `J`
  set ū : T ⧸ J := ψ (IsLocalization.Away.invSelf a)
  have hū : ū * θ a = 1 := by
    show ψ _ * ψ (algebraMap A Aa a) = 1
    rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  -- a right inverse of the Jacobian matrix modulo `J`
  let Mbar : Matrix (Fin c) (Fin n) (T ⧸ J) :=
    Matrix.of fun j i => θ (φ (pderiv i (f (Fin.castLE hcm j))))
  obtain ⟨Nbar, hN⟩ := exists_right_inverse_of_mem_span θ.toRingHom Mbar
    (fun e => φ (Matrix.det fun j k : Fin c => pderiv (e k) (f (Fin.castLE hcm j))))
    (fun e => by
      show θ (φ (Matrix.det (Matrix.of fun j k : Fin c =>
        pderiv (e k) (f (Fin.castLE hcm j))))) = _
      rw [AlgHom.map_det, AlgHom.map_det]
      congr 1)
    hmem hū
  choose Ñ hÑ using fun i k => Ideal.Quotient.mk_surjective (Nbar i k)
  let fc : Fin c → T := fun k => aeval t (f (Fin.castLE hcm k))
  let δ : Fin n → T := fun i => -∑ k, Ñ i k * fc k
  have hδJ : ∀ i, δ i ∈ J := fun i =>
    J.neg_mem (J.sum_mem fun k _ => J.mul_mem_left _ (hfJ _))
  have hδδ : ∀ i j, δ i * δ j = 0 := fun i j => hJsq _ (hδJ i) _ (hδJ j)
  have htaylor := aeval_add_of_mul_eq_zero (R := R) t δ hδδ
  have hev' : ∀ p, aeval (t + δ) p - aeval t p ∈ J := fun p => by
    rw [htaylor, add_sub_cancel_left]
    exact J.sum_mem fun i _ => J.mul_mem_left _ (hδJ i)
  have hmk' : ∀ p, Ideal.Quotient.mk J (aeval (t + δ) p) = θ (φ p) := fun p => by
    rw [← hev p]
    exact Ideal.Quotient.eq.mpr (hev' p)
  -- the first `c` equations vanish at `t + δ`
  have hc0 : ∀ k : Fin c, aeval (t + δ) (f (Fin.castLE hcm k)) = 0 := by
    intro k
    set F := f (Fin.castLE hcm k)
    have hprod : ∀ l, (∑ i, aeval t (pderiv i F) * Ñ i l) - (if k = l then 1 else 0) ∈ J := by
      intro l
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
      have h := congrFun (congrFun hN k) l
      simp only [Matrix.mul_apply, Matrix.one_apply, Mbar, Matrix.of_apply] at h
      simp only [map_mul, hev, hÑ, apply_ite (Ideal.Quotient.mk J), map_one, map_zero]
      rw [h, sub_self]
    have hsum : ∑ i, aeval t (pderiv i F) * δ i =
        -∑ l, (∑ i, aeval t (pderiv i F) * Ñ i l) * fc l := by
      simp only [δ, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun i _ => by ring)
    have hterm : ∀ l, (∑ i, aeval t (pderiv i F) * Ñ i l) * fc l =
        (if k = l then 1 else 0) * fc l := fun l => by
      have h := hJsq _ (hprod l) _ (hfJ (Fin.castLE hcm l))
      rw [sub_mul] at h
      exact sub_eq_zero.mp h
    rw [htaylor, hsum, Finset.sum_congr rfl fun l _ => hterm l]
    simp [fc, F]
  have hJimg : ∀ j, aeval (t + δ) (f j) ∈ J := fun j => by
    have h := J.add_mem (hev' (f j)) (hfJ j)
    rwa [sub_add_cancel] at h
  -- `g` becomes a unit
  have hgu : IsUnit (aeval (t + δ) g) := by
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ū
    have h3 : aeval (t + δ) g * v - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk', hg, hv, map_one, mul_comm, hū,
        sub_self]
    have hz := hJsq _ h3 _ h3
    refine IsUnit.of_mul_eq_one (v * (1 - (aeval (t + δ) g * v - 1))) ?_
    linear_combination (-1 : T) * hz
  -- all equations vanish at `t + δ`
  have hall : ∀ j, aeval (t + δ) (f j) = 0 := by
    intro j
    by_cases hj : (j : ℕ) < c
    · have h := hc0 ⟨j, hj⟩
      rwa [show Fin.castLE hcm ⟨j, hj⟩ = j from Fin.ext rfl] at h
    · push Not at hj
      have h1 := Ideal.mem_map_of_mem (aeval (t + δ) : MvPolynomial (Fin n) R →ₐ[R] T) (hgf j hj)
      have hbot : Ideal.map (aeval (t + δ) : MvPolynomial (Fin n) R →ₐ[R] T)
          (Ideal.span (f '' {i | (i : ℕ) < c}) ⊔ Ideal.span (Set.range f) ^ 2) = ⊥ := by
        rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span]
        have hA : Ideal.span ((aeval (t + δ) : MvPolynomial (Fin n) R →ₐ[R] T) ''
            (f '' {i | (i : ℕ) < c})) = ⊥ := by
          rw [Ideal.span_eq_bot]
          rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
          have h := hc0 ⟨i, hi⟩
          rwa [show Fin.castLE hcm ⟨i, hi⟩ = i from Fin.ext rfl] at h
        have hB : Ideal.span ((aeval (t + δ) : MvPolynomial (Fin n) R →ₐ[R] T) '' Set.range f) ≤ J := by
          rw [Ideal.span_le]
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact hJimg i
        rw [hA, bot_sup_eq, eq_bot_iff, ← hJ]
        exact Ideal.pow_right_mono hB 2
      rw [hbot, Ideal.mem_bot, map_mul] at h1
      exact (hgu.mul_right_eq_zero).mp h1
  -- descend to `A` and to `A_a`
  let ev' : MvPolynomial (Fin n) R →ₐ[R] T := aeval (t + δ)
  have hkerle : RingHom.ker φ.toRingHom ≤ RingHom.ker ev'.toRingHom := by
    show RingHom.ker φ ≤ _
    rw [hker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hall j
  let ρ : A →ₐ[R] T := AlgHom.liftOfSurjective φ hφ ev' hkerle
  have hρ : ∀ p, ρ (φ p) = aeval (t + δ) p := AlgHom.liftOfSurjective_apply φ hφ ev' hkerle
  have hρa : IsUnit (ρ.toRingHom a) := by
    show IsUnit (ρ a)
    rw [← hg, hρ]
    exact hgu
  let ρ₀ : Aa →+* T := IsLocalization.Away.lift a hρa
  let lift : Aa →ₐ[R] T :=
    { ρ₀ with
      commutes' := fun r => by
        show ρ₀ (algebraMap R Aa r) = _
        rw [IsScalarTower.algebraMap_apply R A Aa, IsLocalization.Away.lift_eq]
        exact ρ.commutes r }
  refine ⟨lift, ?_⟩
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext x
  obtain ⟨p, rfl⟩ := hφ x
  show Ideal.Quotient.mk J (ρ₀ (algebraMap A Aa (φ p))) = ψ (algebraMap A Aa (φ p))
  rw [IsLocalization.Away.lift_eq]
  show Ideal.Quotient.mk J (ρ (φ p)) = _
  rw [hρ, hmk']
  rfl

end Langlands.CommutativeAlgebra.Popescu
