import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Langlands.Representation.Archimedean.ComplexJacquetFinite

/-!
# Invariants of finite-dimensional `𝔤𝔩_n(ℂ)`-modules with integral weights

Let `e_pq` (`p, q < n`) be operators on a finite-dimensional complex vector space `V` satisfying
the commutation relations of the matrix units of `𝔤𝔩_n(ℂ)` (`IsGlFamily`), such that `V` is
spanned by weight vectors with integral weights (`IntWeights`). The Casimir operator
`c = Σ_{p,q} e_pq e_qp` commutes with every `e_pq`. We show:

* `eq_zero_of_isNilpotent_cas`: if `c` is nilpotent, then all `e_pq` vanish;
* `apply_mem_range_cas_pow`: every `e_pq` maps `V` into `range (c ^ N)`;
* `exists_invariant_lift`: invariants lift along equivariant surjections whose source has
  integral weights.

The proof of the first statement takes a lowest weight vector `v` of weight `μ` (killed by
the `e_pq`, `q < p`). The `𝔰𝔩₂`-triples `(e_pp - e_qq, e_pq, e_qp)` (Mathlib's `IsSl2Triple`)
show `μ_p - μ_q ∈ ℕ` for `q < p`, and `c v = (Σ_p μ_p² + Σ_{q<p} (μ_p - μ_q)) v`. Since `c` is
nilpotent, this scalar vanishes, so `μ = 0`, and then `v` is invariant. Induction on the
dimension (passing to the quotient by `ℂ v`) finishes the proof.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GLReynolds

open ComplexJacquetFinite Module

universe u

section Family

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- `v` is a weight vector of integral weight `μ`: `e_pp v = μ_p v` for all `p`. -/
def IsWeightVec (e : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℤ) (v : V) : Prop :=
  ∀ p, e p p v = ((μ p : ℤ) : ℂ) • v

/-- `V` is spanned by weight vectors with integral weights. -/
def IntWeights (e : Fin n → Fin n → Module.End ℂ V) : Prop :=
  Submodule.span ℂ {v | ∃ μ : Fin n → ℤ, IsWeightVec e μ v} = ⊤

/-- The Casimir operator `c = Σ_{p,q} e_pq e_qp`. -/
def cas (e : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ p, ∑ q, e p q * e q p

variable {e : Fin n → Fin n → Module.End ℂ V}

/-- The Casimir operator commutes with every `e_ab`. -/
theorem cas_comm (he : IsGlFamily e) (a b : Fin n) : e a b * cas e = cas e * e a b := by
  rw [← sub_eq_zero]
  have key : ∀ p q, e a b * (e p q * e q p) - e p q * e q p * e a b =
      (e a b * e p q - e p q * e a b) * e q p + e p q * (e a b * e q p - e q p * e a b) := by
    intro p q; noncomm_ring
  simp only [cas, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key, he a b]
  simp only [sub_mul, mul_sub, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  abel

theorem cas_apply_comm (he : IsGlFamily e) (a b : Fin n) (v : V) :
    e a b (cas e v) = cas e (e a b v) := by
  rw [← Module.End.mul_apply, cas_comm he, Module.End.mul_apply]

theorem cas_pow_apply_comm (he : IsGlFamily e) (a b : Fin n) (k : ℕ) (v : V) :
    e a b ((cas e ^ k) v) = (cas e ^ k) (e a b v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, cas_apply_comm he]

/-! ### Weights -/

/-- The height `Σ_r r μ_r` of an integral weight. -/
def ht (μ : Fin n → ℤ) : ℤ := ∑ r : Fin n, ((r : ℕ) : ℤ) * μ r

theorem ht_shift (μ : Fin n → ℤ) (p q : Fin n) :
    ht (μ + Pi.single p 1 - Pi.single q 1) = ht μ + p - q := by
  simp only [ht, Pi.sub_apply, Pi.add_apply, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem isWeightVec_shift (he : IsGlFamily e) {μ : Fin n → ℤ} {v : V} (hv : IsWeightVec e μ v)
    {p q : Fin n} (hpq : p ≠ q) :
    IsWeightVec e (μ + Pi.single p 1 - Pi.single q 1) (e p q v) := by
  intro r
  have h := LinearMap.congr_fun (he r r p q) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv r, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hrp : r = p
  · subst hrp
    have hqr : ¬ q = r := fun h => hpq h.symm
    simp [hpq, hqr, add_smul]
    abel
  · by_cases hrq : r = q
    · subst hrq
      simp [hrp, sub_smul]
      abel
    · have hqr : ¬ q = r := fun h => hrq h.symm
      simp [hrp, hrq, hqr]

/-- A nonzero `V` spanned by integral weight vectors contains a lowest weight vector: a nonzero
weight vector killed by all `e_pq` with `q < p`. -/
theorem exists_lowest [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hw : IntWeights e) :
    ∃ v : V, v ≠ 0 ∧ ∃ μ : Fin n → ℤ, IsWeightVec e μ v ∧ ∀ p q, q < p → e p q v = 0 := by
  classical
  set H : Module.End ℂ V := ∑ r : Fin n, ((r : ℕ) : ℂ) • e r r with hHdef
  have hH : ∀ μ v, IsWeightVec e μ v → H v = ((ht μ : ℤ) : ℂ) • v := by
    intro μ v hv
    have hv' : ∀ r, e r r v = ((μ r : ℤ) : ℂ) • v := hv
    simp only [hHdef, LinearMap.sum_apply, LinearMap.smul_apply, hv', smul_smul,
      ht, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_smul]
  let S : Set ℤ := {k | ∃ v : V, v ≠ 0 ∧ ∃ μ, IsWeightVec e μ v ∧ ht μ = k}
  have hfin : S.Finite := by
    refine (H.finite_hasEigenvalue.preimage Int.cast_injective.injOn).subset ?_
    rintro k ⟨v, hv0, μ, hμ, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hH μ v hμ), hv0⟩
  have hne : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    have hbot : Submodule.span ℂ {v | ∃ μ : Fin n → ℤ, IsWeightVec e μ v} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro v ⟨μ, hμ⟩
      by_contra hv0
      have : ht μ ∈ S := ⟨v, hv0, μ, hμ, rfl⟩
      rw [hS] at this
      exact this
    rw [hw] at hbot
    exact top_ne_bot hbot
  obtain ⟨k, ⟨v, hv0, μ, hμ, rfl⟩, hmax⟩ := Set.exists_max_image S id hfin hne
  refine ⟨v, hv0, μ, hμ, fun p q hqp => ?_⟩
  by_contra hne0
  have hmem : ht (μ + Pi.single p 1 - Pi.single q 1) ∈ S :=
    ⟨e p q v, hne0, _, isWeightVec_shift he hμ (ne_of_gt hqp), rfl⟩
  have := hmax _ hmem
  rw [ht_shift] at this
  simp only [id] at this
  have : (q : ℤ) < p := by exact_mod_cast hqp
  omega

/-! ### `𝔰𝔩₂` integrality -/

/-- `𝔰𝔩₂` integrality: a nonzero vector `v` with `x v = 0` and `h v = μ v` in a
finite-dimensional module has `μ ∈ ℕ`, and if `μ = 0` then also `y v = 0`. -/
theorem sl2_nat [FiniteDimensional ℂ V] {h x y : Module.End ℂ V} (hxy : x * y - y * x = h)
    (hhx : h * x - x * h = 2 • x) (hhy : h * y - y * h = -(2 • y)) {v : V} (hv : v ≠ 0) {μ : ℂ}
    (hh : h v = μ • v) (hx : x v = 0) : (∃ k : ℕ, μ = k) ∧ (μ = 0 → y v = 0) := by
  by_cases h0 : h = 0
  · subst h0
    have hμ : μ = 0 := by
      have : μ • v = 0 := by rw [← hh]; rfl
      exact (smul_eq_zero.mp this).resolve_right hv
    refine ⟨⟨0, by simp [hμ]⟩, fun _ => ?_⟩
    have hy : (2 : ℂ) • y = 0 := by
      have : -(2 • y) = (0 : Module.End ℂ V) := by rw [← hhy]; simp
      rw [neg_eq_zero] at this
      rw [← this, ofNat_smul_eq_nsmul]
    have : y = 0 := (smul_eq_zero.mp hy).resolve_left two_ne_zero
    simp [this]
  · have t : IsSl2Triple h x y :=
      { h_ne_zero := h0
        lie_e_f := by rw [LieRing.of_associative_ring_bracket]; exact hxy
        lie_h_e_nsmul := by rw [LieRing.of_associative_ring_bracket]; exact hhx
        lie_h_f_nsmul := by rw [LieRing.of_associative_ring_bracket]; exact hhy }
    have P : t.HasPrimitiveVectorWith v μ :=
      { ne_zero := hv
        lie_h := by rw [Module.End.lie_apply]; exact hh
        lie_e := by rw [Module.End.lie_apply]; exact hx }
    refine ⟨P.exists_nat, fun hμ => ?_⟩
    have := P.pow_toEnd_f_eq_zero_of_eq_nat (n := 0) (by simp [hμ])
    simpa using this

/-- The `𝔰𝔩₂`-relations for the triple `(e_pp - e_qq, e_pq, e_qp)`, `p ≠ q`. -/
theorem sl2_rel (he : IsGlFamily e) {p q : Fin n} (hpq : p ≠ q) :
    e p q * e q p - e q p * e p q = e p p - e q q ∧
      (e p p - e q q) * e p q - e p q * (e p p - e q q) = 2 • e p q ∧
      (e p p - e q q) * e q p - e q p * (e p p - e q q) = -(2 • e q p) := by
  have hqp : q ≠ p := fun h => hpq h.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [he p q q p]; simp
  · have h1 := he p p p q
    have h2 := he q q p q
    simp only [ite_true, hqp, ite_false] at h1 h2
    have : (e p p - e q q) * e p q - e p q * (e p p - e q q) =
        (e p p * e p q - e p q * e p p) - (e q q * e p q - e p q * e q q) := by noncomm_ring
    rw [this, h1, h2, two_nsmul]
    simp
  · have h1 := he p p q p
    have h2 := he q q q p
    simp only [ite_true, hpq, ite_false] at h1 h2
    have : (e p p - e q q) * e q p - e q p * (e p p - e q q) =
        (e p p * e q p - e q p * e p p) - (e q q * e q p - e q p * e q q) := by noncomm_ring
    rw [this, h1, h2, two_nsmul]
    simp only [zero_sub, sub_zero, neg_add_rev]
    abel

/-! ### The Casimir operator on a lowest weight vector -/

theorem cas_apply_lowest (he : IsGlFamily e) {μ : Fin n → ℤ} {v : V} (hμ : IsWeightVec e μ v)
    (hlow : ∀ p q, q < p → e p q v = 0) :
    cas e v = (((∑ p, μ p ^ 2 + ∑ p, ∑ q, if q < p then μ p - μ q else 0 : ℤ)) : ℂ) • v := by
  have hterm : ∀ p q, (e p q * e q p) v =
      (((if p = q then μ p ^ 2 else 0) + (if q < p then μ p - μ q else 0) : ℤ) : ℂ) • v := by
    intro p q
    rw [Module.End.mul_apply]
    rcases lt_trichotomy q p with hqp | rfl | hpq
    · have h := LinearMap.congr_fun (he p q q p) v
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hlow p q hqp, map_zero, sub_zero,
        ite_true] at h
      rw [h, hμ p, hμ q, ← sub_smul]
      simp [ne_of_gt hqp, hqp]
    · simp [hμ q, smul_smul, sq]
    · rw [hlow q p hpq, map_zero]
      simp [ne_of_lt hpq, not_lt.mpr hpq.le]
  have hsum : ∑ p, ∑ q, ((if p = q then μ p ^ 2 else 0) + (if q < p then μ p - μ q else 0) : ℤ) =
      ∑ p, μ p ^ 2 + ∑ p, ∑ q, (if q < p then μ p - μ q else 0) := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [cas, LinearMap.sum_apply, hterm, ← Finset.sum_smul]
  congr 1
  rw [← hsum]
  simp only [Int.cast_sum]

/-! ### Nilpotent Casimir forces a trivial action -/

/-- Integral eigenvalues: for each `p`, the operator `e_pp` is annihilated by a polynomial
`X · Π_{k ∈ s} (X - k)` with `s` a finite set of nonzero integers. -/
theorem exists_poly_eq_zero [FiniteDimensional ℂ V] (hw : IntWeights e) (p : Fin n) :
    ∃ s : Finset ℤ, 0 ∉ s ∧ Polynomial.aeval (e p p)
      (Polynomial.X * ∏ k ∈ s, (Polynomial.X - Polynomial.C (k : ℂ))) = 0 := by
  classical
  set T := {v : V | ∃ μ : Fin n → ℤ, IsWeightVec e μ v}
  obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℂ T
  have hbfin : b.Finite := hbli.setFinite
  have hm : ∀ v ∈ b, ∃ μ : Fin n → ℤ, IsWeightVec e μ v := fun v hv => hbT hv
  choose! M hM using hm
  refine ⟨(hbfin.toFinset.image (fun v => M v p)).erase 0, Finset.notMem_erase _ _, ?_⟩
  apply LinearMap.ext_on_range (v := (Subtype.val : b → V))
  · rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan, hw]
  · rintro ⟨v, hv⟩
    have hev : e p p v = ((M v p : ℤ) : ℂ) • v := hM v hv p
    rw [LinearMap.zero_apply, Module.End.aeval_apply_of_mem_apply_eq_smul hev]
    apply smul_eq_zero_of_left
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod]
    by_cases h0 : M v p = 0
    · simp [h0]
    · apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := M v p)
      · exact Finset.mem_erase.mpr ⟨h0, Finset.mem_image.mpr ⟨v, hbfin.mem_toFinset.mpr hv, rfl⟩⟩
      · simp

/-- The operators `e_pp` are semisimple: `e_pp² v = 0` implies `e_pp v = 0`. -/
theorem apply_eq_zero_of_sq [FiniteDimensional ℂ V] (hw : IntWeights e) (p : Fin n) {v : V}
    (hv : e p p (e p p v) = 0) : e p p v = 0 := by
  classical
  obtain ⟨s, hs0, hs⟩ := exists_poly_eq_zero hw p
  set Q : Polynomial ℂ := ∏ k ∈ s, (Polynomial.X - Polynomial.C (k : ℂ)) with hQ
  have hw0 : e p p (e p p v) = (0 : ℂ) • e p p v := by rw [hv, zero_smul]
  have h1 : Polynomial.aeval (e p p) Q (e p p v) = 0 := by
    have := LinearMap.congr_fun hs v
    rwa [mul_comm, map_mul, Module.End.mul_apply, Polynomial.aeval_X,
      LinearMap.zero_apply] at this
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hw0] at h1
  refine (smul_eq_zero.mp h1).resolve_left ?_
  rw [hQ, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  have : k ≠ 0 := fun h => hs0 (h ▸ hk)
  simpa using this

/-- If the Casimir operator is nilpotent, a nonzero `V` has a nonzero invariant vector: a lowest
weight vector has Casimir eigenvalue `Σ_p μ_p² + Σ_{q<p} (μ_p - μ_q)`, a sum of nonnegative
integers, which must vanish; then `μ = 0` and `𝔰𝔩₂` theory kills `v` by the upper `e_pq`. -/
theorem exists_invariant [FiniteDimensional ℂ V] [Nontrivial V] (he : IsGlFamily e)
    (hw : IntWeights e) (hc : IsNilpotent (cas e)) : ∃ v : V, v ≠ 0 ∧ ∀ p q, e p q v = 0 := by
  obtain ⟨v, hv0, μ, hμ, hlow⟩ := exists_lowest he hw
  -- `μ_p - μ_q ∈ ℕ` for `q < p`
  have hnat : ∀ p q, q < p → 0 ≤ μ p - μ q := by
    intro p q hqp
    obtain ⟨h1, h2, h3⟩ := sl2_rel he (ne_of_gt hqp)
    have hh : (e p p - e q q) v = (((μ p - μ q : ℤ)) : ℂ) • v := by
      rw [LinearMap.sub_apply, hμ p, hμ q, ← sub_smul]; push_cast; rfl
    obtain ⟨⟨k, hk⟩, -⟩ := sl2_nat h1 h2 h3 hv0 hh (hlow p q hqp)
    have : μ p - μ q = k := by exact_mod_cast hk
    omega
  -- the Casimir eigenvalue vanishes
  set s : ℤ := ∑ p, μ p ^ 2 + ∑ p, ∑ q, if q < p then μ p - μ q else 0 with hsdef
  have hcv := cas_apply_lowest he hμ hlow
  rw [← hsdef] at hcv
  have hs0 : s = 0 := by
    obtain ⟨k, hk⟩ := hc
    have hpow : ∀ j : ℕ, (cas e ^ j) v = ((s : ℂ) ^ j) • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, hcv, map_smul, ih, smul_smul, pow_succ, mul_comm]
    have := hpow k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    have := (this.resolve_right hv0)
    exact_mod_cast pow_eq_zero_iff'.mp this |>.1
  have hμ0 : ∀ p, μ p = 0 := by
    have h1 : 0 ≤ ∑ p, ∑ q, (if q < p then μ p - μ q else 0) :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by
        split_ifs with h
        · exact hnat p q h
        · exact le_rfl
    have h2 : ∑ p, μ p ^ 2 = 0 := by
      have h3 : 0 ≤ ∑ p, μ p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
      omega
    intro p
    have := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => sq_nonneg (μ p)).mp h2 p
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  refine ⟨v, hv0, fun p q => ?_⟩
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · exact hlow p q hqp
  · rw [hμ q, hμ0 q]; simp
  · -- use the triple `(e_qq - e_pp, e_qp, e_pq)`
    obtain ⟨h1, h2, h3⟩ := sl2_rel he (ne_of_gt hpq)
    have hh : (e q q - e p p) v = ((0 : ℤ) : ℂ) • v := by
      rw [LinearMap.sub_apply, hμ p, hμ q, hμ0 p, hμ0 q]; simp
    exact (sl2_nat h1 h2 h3 hv0 hh (hlow q p hpq)).2 (by simp)

end Family

/-! ### Quotients -/

section Quotient

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {e : Fin n → Fin n → Module.End ℂ V}

/-- The family induced on the quotient by a stable subspace. -/
def qFam (S : Submodule ℂ V) (hS : ∀ p q, S ≤ S.comap (e p q)) :
    Fin n → Fin n → Module.End ℂ (V ⧸ S) :=
  fun p q => S.mapQ S (e p q) (hS p q)

variable (S : Submodule ℂ V) (hS : ∀ p q, S ≤ S.comap (e p q))

theorem qFam_mk (p q : Fin n) (x : V) :
    qFam S hS p q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e p q x) :=
  Submodule.mapQ_apply S S (e p q) x

theorem isGlFamily_qFam (he : IsGlFamily e) : IsGlFamily (qFam S hS) := by
  intro a b c d
  apply Submodule.linearMap_qext
  ext x
  have h := LinearMap.congr_fun (he a b c d) x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply,
    Module.End.mul_apply, qFam_mk] at h ⊢
  rw [← Submodule.Quotient.mk_sub, h]
  split_ifs <;> simp [qFam_mk]

theorem intWeights_qFam (hw : IntWeights e) : IntWeights (qFam S hS) := by
  rw [IntWeights, eq_top_iff]
  have hmap : Submodule.map S.mkQ ⊤ = ⊤ := by rw [Submodule.map_top, Submodule.range_mkQ]
  rw [← hmap, ← hw, Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨v, ⟨μ, hμ⟩, rfl⟩
  refine ⟨μ, fun p => ?_⟩
  simp only [Submodule.mkQ_apply, qFam_mk, hμ p, Submodule.Quotient.mk_smul]

theorem cas_qFam_mk (x : V) :
    cas (qFam S hS) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (cas e x) := by
  simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, qFam_mk]
  simp only [← Submodule.mkQ_apply, map_sum]

theorem cas_qFam_pow_mk (k : ℕ) (x : V) :
    (cas (qFam S hS) ^ k) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((cas e ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, cas_qFam_mk, ih]

end Quotient

/-! ### The main theorem -/

/-- `eq_zero_of_isNilpotent_cas` for modules of dimension `d`, by strong induction on `d`. -/
theorem eq_zero_of_isNilpotent_cas_aux (d : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {n : ℕ}
      (e : Fin n → Fin n → Module.End ℂ V), finrank ℂ V = d → IsGlFamily e → IntWeights e →
      IsNilpotent (cas e) → ∀ p q, e p q = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ n e hd he hw hc p q
  rcases subsingleton_or_nontrivial V with hV | hV
  · ext x; exact Subsingleton.elim _ _
  obtain ⟨v₀, hv₀, hinv⟩ := exists_invariant he hw hc
  set S : Submodule ℂ V := ℂ ∙ v₀
  have hS : ∀ p q, S ≤ S.comap (e p q) := by
    intro p q x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [Submodule.mem_comap, hinv]
  have hlt : finrank ℂ (V ⧸ S) < d := by
    have h1 := S.finrank_quotient_add_finrank
    have h2 : finrank ℂ S = 1 := finrank_span_singleton hv₀
    omega
  have hcq : IsNilpotent (cas (qFam S hS)) := by
    obtain ⟨k, hk⟩ := hc
    refine ⟨k, ?_⟩
    apply Submodule.linearMap_qext
    ext x
    simp [cas_qFam_pow_mk, hk]
  have hq := ih _ hlt (V ⧸ S) (qFam S hS) rfl (isGlFamily_qFam S hS he)
    (intWeights_qFam S hS hw) hcq
  -- every `e_ab x` lies in `ℂ v₀`, hence is invariant
  have hmem : ∀ a b x, e a b x ∈ S := by
    intro a b x
    have := LinearMap.congr_fun (hq a b) (Submodule.Quotient.mk x)
    rwa [qFam_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
  have hkill : ∀ a b c d x, e a b (e c d x) = 0 := by
    intro a b c d x
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hmem c d x)
    rw [← ht, map_smul, hinv, smul_zero]
  ext x
  rw [LinearMap.zero_apply]
  by_cases hpq : p = q
  · subst hpq
    exact apply_eq_zero_of_sq hw p (hkill p p p p x)
  · have hqp : ¬ q = p := fun h => hpq h.symm
    have h := LinearMap.congr_fun (he p p p q) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hkill] at h
    simp [hqp] at h
    first | exact h | exact h.symm

/-- If the Casimir operator is nilpotent on a finite-dimensional module with integral weights,
the module is trivial. -/
theorem eq_zero_of_isNilpotent_cas {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ} {e : Fin n → Fin n → Module.End ℂ V} (he : IsGlFamily e)
    (hw : IntWeights e) (hc : IsNilpotent (cas e)) (p q : Fin n) : e p q = 0 :=
  eq_zero_of_isNilpotent_cas_aux _ V e rfl he hw hc p q

/-- Every `e_pq` maps `V` into `range (c ^ N)`. -/
theorem apply_mem_range_cas_pow {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ} {e : Fin n → Fin n → Module.End ℂ V} (he : IsGlFamily e)
    (hw : IntWeights e) (N : ℕ) (p q : Fin n) (x : V) :
    e p q x ∈ LinearMap.range (cas e ^ N) := by
  set S := LinearMap.range (cas e ^ N)
  have hS : ∀ p q, S ≤ S.comap (e p q) := by
    rintro p q _ ⟨y, rfl⟩
    exact ⟨e p q y, (cas_pow_apply_comm he p q N y).symm⟩
  have hcq : IsNilpotent (cas (qFam S hS)) := by
    refine ⟨N, ?_⟩
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, cas_qFam_pow_mk,
      LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ x
  have := LinearMap.congr_fun (eq_zero_of_isNilpotent_cas (isGlFamily_qFam S hS he)
    (intWeights_qFam S hS hw) hcq p q) (Submodule.Quotient.mk x)
  rwa [qFam_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this

/-- **Invariant lifting.** Let `φ : V → W` be a surjective linear map between
finite-dimensional modules intertwining families `e` and `f` satisfying the `𝔤𝔩_n`-relations,
where `V` has integral weights. Every invariant `y ∈ W` is `φ x` for an invariant `x ∈ V`. -/
theorem exists_invariant_lift {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    {e : Fin n → Fin n → Module.End ℂ V} {f : Fin n → Fin n → Module.End ℂ W}
    (he : IsGlFamily e) (hw : IntWeights e) (φ : V →ₗ[ℂ] W)
    (hφ : Function.Surjective φ) (hφe : ∀ p q x, φ (e p q x) = f p q (φ x)) {y : W}
    (hy : ∀ p q, f p q y = 0) : ∃ x : V, (∀ p q, e p q x = 0) ∧ φ x = y := by
  obtain ⟨N, hN1, hNV, hNW⟩ := ((Filter.eventually_ge_atTop 1).and
    ((cas e).eventually_isCompl_ker_pow_range_pow.and
      (cas f).eventually_isCompl_ker_pow_range_pow)).exists
  have hφc : ∀ x, φ (cas e x) = cas f (φ x) := by
    intro x
    simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hφe]
  have hφcN : ∀ k x, φ ((cas e ^ k) x) = (cas f ^ k) (φ x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hφc]
  obtain ⟨x', rfl⟩ := hφ y
  have hx' : x' ∈ LinearMap.ker (cas e ^ N) ⊔ LinearMap.range (cas e ^ N) := by
    rw [hNV.sup_eq_top]; trivial
  obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp hx'
  -- `φ r` lies in the kernel and in the range of `c ^ N` on `W`
  have hyker : (cas f ^ N) (φ (k + r)) = 0 := by
    obtain ⟨N', rfl⟩ := Nat.exists_eq_add_of_le' hN1
    rw [pow_succ, Module.End.mul_apply]
    have : cas f (φ (k + r)) = 0 := by
      simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, hy, map_zero,
        Finset.sum_const_zero]
    rw [this, map_zero]
  have hφk : (cas f ^ N) (φ k) = 0 := by rw [← hφcN, LinearMap.mem_ker.mp hk, map_zero]
  have hφr : φ r ∈ LinearMap.range (cas f ^ N) := by
    obtain ⟨z, rfl⟩ := hr
    exact ⟨φ z, (hφcN N z).symm⟩
  have hφr0 : φ r = 0 := by
    have hker : φ r ∈ LinearMap.ker (cas f ^ N) := by
      rw [LinearMap.mem_ker]
      have : φ r = φ (k + r) - φ k := by rw [map_add]; abel
      rw [this, map_sub, hyker, hφk, sub_zero]
    have := hNW.disjoint.le_bot ⟨hker, hφr⟩
    simpa using this
  refine ⟨k, fun p q => ?_, by rw [map_add, hφr0, add_zero]⟩
  -- `e_pq k` lies in the kernel and in the range of `c ^ N` on `V`
  have hker : e p q k ∈ LinearMap.ker (cas e ^ N) := by
    rw [LinearMap.mem_ker, ← cas_pow_apply_comm he, LinearMap.mem_ker.mp hk, map_zero]
  have := hNV.disjoint.le_bot ⟨hker, apply_mem_range_cas_pow he hw N p q k⟩
  simpa using this

end GLReynolds

end Langlands.Archimedean
