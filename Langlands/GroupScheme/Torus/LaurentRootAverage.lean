import Langlands.GroupScheme.Torus.UniversalPoint
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.GeomSum

/-! # Constant Laurent coefficients as integral combinations of evaluations -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.splitTorus

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]
  {A : Type v} [CommRing A] [Algebra k A]

/-- Evaluation of Laurent polynomials with coefficients in `A` at a point of `(kˣ)^I`. -/
def laurentEval (ζ : I → kˣ) : AddMonoidAlgebra A (I → ℤ) →ₐ[k] A :=
  (AddMonoidAlgebra.lift A A (I → ℤ)
    ((algebraMap k A).toMonoidHom.comp ((Units.coeHom k).comp (exponentValue I ζ)))).restrictScalars k

omit [DecidableEq I] in
theorem laurentEval_apply (ζ : I → kˣ) (f : AddMonoidAlgebra A (I → ℤ)) :
    laurentEval I ζ f =
      f.coeff.sum fun m b => b * algebraMap k A (exponentValue I ζ (Multiplicative.ofAdd m) : k) := by
  rw [laurentEval, AlgHom.restrictScalars_apply, AddMonoidAlgebra.lift_apply]
  rfl

/-- The sum of a character over the `ℓ`-torsion points of `(kˣ)^I`. -/
theorem sum_exponentValue_pow {ℓ : ℕ} {ω : kˣ} (hω : IsPrimitiveRoot ω ℓ) (m : I → ℤ)
    (hm : ∀ i, (m i).natAbs < ℓ) :
    ∑ x : I → Fin ℓ, ((exponentValue I (fun i => ω ^ (x i : ℕ)) (Multiplicative.ofAdd m) : kˣ) : k) =
      if m = 0 then (ℓ : k) ^ Fintype.card I else 0 := by
  have e (x : I → Fin ℓ) :
      ((exponentValue I (fun i => ω ^ (x i : ℕ)) (Multiplicative.ofAdd m) : kˣ) : k) =
        ∏ i, (((ω ^ m i : kˣ) : k)) ^ (x i : ℕ) := by
    change ((∏ i, (ω ^ (x i : ℕ)) ^ m i : kˣ) : k) = _
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm]
  simp_rw [e]
  rw [← Fintype.prod_sum (fun (i : I) (j : Fin ℓ) => (((ω ^ m i : kˣ) : k)) ^ (j : ℕ))]
  have hfac (i : I) :
      ∑ j : Fin ℓ, (((ω ^ m i : kˣ) : k)) ^ (j : ℕ) = if m i = 0 then (ℓ : k) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (((ω ^ m i : kˣ) : k)) ^ j)]
    split_ifs with hmi
    · simp [hmi]
    · have hne : ((ω ^ m i : kˣ) : k) - 1 ≠ 0 := by
        rw [sub_ne_zero, Ne, ← Units.val_one, Units.val_inj, hω.zpow_eq_one_iff_dvd]
        intro hdvd
        exact hmi (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hm i))
      have hpow : (((ω ^ m i : kˣ) : k)) ^ ℓ = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
          zpow_natCast, hω.pow_eq_one, one_zpow, Units.val_one]
      have h := geom_sum_mul (((ω ^ m i : kˣ) : k)) ℓ
      rw [hpow, sub_self] at h
      exact (mul_eq_zero.1 h).resolve_right hne
  simp_rw [hfac]
  split_ifs with hm0
  · simp [hm0]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hm0
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Summing the evaluations at the `ℓ`-torsion points multiplies the constant coefficient by
`ℓ ^ |I|`, provided all exponents occurring in the polynomial have absolute value below `ℓ`. -/
theorem sum_laurentEval {ℓ : ℕ} {ω : kˣ} (hω : IsPrimitiveRoot ω ℓ)
    (f : AddMonoidAlgebra A (I → ℤ)) (hf : ∀ e ∈ f.coeff.support, ∀ i, (e i).natAbs < ℓ) :
    ∑ x : I → Fin ℓ, laurentEval I (fun i => ω ^ (x i : ℕ)) f =
      (ℓ ^ Fintype.card I : ℕ) • f.coeff 0 := by
  simp_rw [laurentEval_apply]
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← map_sum]
  rw [Finset.sum_congr rfl fun e he => by rw [sum_exponentValue_pow I hω e (hf e he)]]
  rw [Finset.sum_eq_single (0 : I → ℤ)]
  · rw [ite_eq_left rfl, map_pow, map_natCast, nsmul_eq_mul, Nat.cast_pow, mul_comm]
  · intro e _ he
    rw [ite_eq_right he, map_zero, mul_zero]
  · intro h
    rw [Finsupp.notMem_support_iff.1 h, zero_mul]

omit [DecidableEq I] in
/-- Every natural number not divisible by the characteristic is nonzero in the field. -/
theorem natCast_ne_zero_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (hlt : ringChar k < ℓ) :
    (ℓ : k) ≠ 0 := by
  rw [Ne, ringChar.spec]
  intro h
  rcases hℓ.eq_one_or_self_of_dvd _ h with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

variable (k) in
/-- The constant coefficients of a matrix of Laurent polynomials lie in every additive
subgroup containing all of its evaluations along `k`-algebra homomorphisms. -/
theorem map_coeff_zero_mem [IsAlgClosed k] {m n : Type*} [Fintype m] [Fintype n]
    (S : AddSubgroup (Matrix m n A)) (M : Matrix m n (AddMonoidAlgebra A (I → ℤ)))
    (hM : ∀ φ : AddMonoidAlgebra A (I → ℤ) →ₐ[k] A, M.map φ ∈ S) :
    M.map (fun f => f.coeff 0) ∈ S := by
  classical
  -- A bound for all exponents occurring in the entries.
  let F : Finset (I → ℤ) := Finset.univ.biUnion fun p : m × n => (M p.1 p.2).coeff.support
  let B : ℕ := F.sup fun e => Finset.univ.sup fun i => (e i).natAbs
  have hB (a : m) (b : n) (e : I → ℤ) (he : e ∈ (M a b).coeff.support) (i : I) :
      (e i).natAbs ≤ B := by
    have heF : e ∈ F := Finset.mem_biUnion.2 ⟨(a, b), Finset.mem_univ _, he⟩
    exact le_trans (Finset.le_sup (f := fun i => (e i).natAbs) (Finset.mem_univ i))
      (Finset.le_sup (f := fun e : I → ℤ => Finset.univ.sup fun i => (e i).natAbs) heF)
  -- For a large prime `ℓ`, the multiple `ℓ ^ |I|` of the constant coefficients lies in `S`.
  have key (ℓ : ℕ) (hℓ : ℓ.Prime) (hBℓ : B < ℓ) (hcℓ : ringChar k < ℓ) :
      (ℓ ^ Fintype.card I : ℕ) • M.map (fun f => f.coeff 0) ∈ S := by
    have : NeZero (ℓ : k) := ⟨natCast_ne_zero_of_prime hℓ hcℓ⟩
    obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k ℓ
    have hω' : IsPrimitiveRoot (hω.isUnit hℓ.ne_zero).unit ℓ :=
      IsPrimitiveRoot.coe_units_iff.1 (by simpa using hω)
    have hsum : (ℓ ^ Fintype.card I : ℕ) • M.map (fun f => f.coeff 0) =
        ∑ x : I → Fin ℓ, M.map (laurentEval I (fun i => (hω.isUnit hℓ.ne_zero).unit ^ (x i : ℕ))) := by
      ext a b
      rw [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
      simp_rw [Matrix.map_apply]
      rw [sum_laurentEval I hω' (M a b) fun e he i => lt_of_le_of_lt (hB a b e he i) hBℓ]
    rw [hsum]
    exact S.sum_mem fun x _ => hM _
  -- Two distinct large primes give coprime multiples.
  obtain ⟨ℓ₁, hℓ₁le, hℓ₁⟩ := Nat.exists_infinite_primes (B + ringChar k + 1)
  obtain ⟨ℓ₂, hℓ₂le, hℓ₂⟩ := Nat.exists_infinite_primes (ℓ₁ + 1)
  have h₁ := key ℓ₁ hℓ₁ (by omega) (by omega)
  have h₂ := key ℓ₂ hℓ₂ (by omega) (by omega)
  have hcop : Nat.Coprime (ℓ₁ ^ Fintype.card I) (ℓ₂ ^ Fintype.card I) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hℓ₁ hℓ₂).2 (by omega))
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h := S.add_mem (S.zsmul_mem h₁ a) (S.zsmul_mem h₂ b)
  rwa [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hab, one_smul] at h

end Langlands.GroupScheme.splitTorus
