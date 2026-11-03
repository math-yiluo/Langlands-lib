import Langlands.Algebra.GradedHopf.BigCell
import Langlands.Algebra.GradedHopf.InvariantDerivation
import Langlands.Algebra.GradedHopf.PolynomialFrobenius
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Homogeneous primitive elements with nonzero differential -/

noncomputable section

open DirectSum TensorProduct MvPolynomial Finsupp

namespace Langlands.Algebra.GradedHopf

section Components

variable {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- Evaluation at homogeneous elements carries weighted homogeneous components to degree
projections. -/
theorem gradeProj_aeval {w : σ → ℤ} {y : σ → A} (hy : ∀ j, y j ∈ 𝒜 (w j))
    (f : MvPolynomial σ k) (d : ℤ) :
    gradeProj 𝒜 d (aeval y f) = aeval y (weightedHomogeneousComponent w d f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : aeval y (monomial m a) ∈ 𝒜 (weight w m) := by
      rw [aeval_monomial, ← Algebra.smul_def, weight_apply]
      exact Submodule.smul_mem _ a (SetLike.prod_pow_mem_graded 𝒜 w y m (fun j _ => hy j))
    have hmon := isWeightedHomogeneous_monomial (R := k) w m a rfl
    by_cases hd : weight w m = d
    · subst hd
      rw [hmon.weightedHomogeneousComponent_same, gradeProj_of_mem_self 𝒜 hm]
    · rw [hmon.weightedHomogeneousComponent_ne d (Ne.symm hd), gradeProj_of_mem_ne 𝒜 hm hd,
        map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

omit [GradedAlgebra 𝒜] in
theorem totalDegree_weightedHomogeneousComponent_le {w : σ → ℤ} (d : ℤ)
    (f : MvPolynomial σ k) : (weightedHomogeneousComponent w d f).totalDegree ≤ f.totalDegree := by
  classical
  refine totalDegree_le_of_support_subset fun m hm => ?_
  rw [MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  rw [MvPolynomial.mem_support_iff]
  split_ifs at hm
  · exact hm
  · exact absurd rfl hm

end Components

section LemmaA

variable {k A σ : Type*} [Field k] [CommRing A] [Bialgebra k A] [IsDomain A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Fintype σ] [DecidableEq σ]
  {w : σ → ℤ} {z : σ → A}

omit [IsDomain A] [GradedAlgebra 𝒜] [Fintype σ] [DecidableEq σ] in
/-- A primitive element given by a constant polynomial is zero. -/
theorem eq_zero_of_isPrimitiveElem_of_eq_C
    (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A)) {f : A}
    (hf : Bialgebra.IsPrimitiveElem k f) {c : k} (hc : (coordEquiv hz).symm f = C c) :
    f = 0 := by
  have hfc : f = algebraMap k A c := by
    rw [← (coordEquiv hz).apply_symm_apply f, hc, ← MvPolynomial.algebraMap_eq,
      AlgEquiv.commutes]
  have h := hf.counit_eq_zero
  rw [hfc, Bialgebra.counit_algebraMap] at h
  rw [hfc, h, map_zero]

omit [IsDomain A] [GradedAlgebra 𝒜] [Fintype σ] [DecidableEq σ] in
/-- The obstruction to primitivity of `x`, read in the polynomial coordinates of `A ⊗ A`. -/
theorem exists_primitivity_defect (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A)) :
    ∃ L : A →ₗ[k] MvPolynomial (σ ⊕ σ) k, (∀ x, L x = 0 ↔ Bialgebra.IsPrimitiveElem k x) ∧
      ∀ (p : ℕ) [Fact p.Prime] [CharP k p] (x : A), L (x ^ p) = L x ^ p := by
  let e := coordEquiv hz
  let Ψ : A ⊗[k] A ≃ₐ[k] MvPolynomial (σ ⊕ σ) k :=
    (Algebra.TensorProduct.congr e.symm e.symm).trans (MvPolynomial.tensorEquivSum k σ σ k)
  let D : A →ₗ[k] A ⊗[k] A :=
    Coalgebra.comul - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1
  have hD : ∀ x, D x = Coalgebra.comul (R := k) x - x ⊗ₜ 1 - 1 ⊗ₜ x := fun x => rfl
  have hL : ∀ x, (Ψ.toLinearMap ∘ₗ D) x =
      Ψ (Coalgebra.comul (R := k) x) - Ψ (x ⊗ₜ 1) - Ψ (1 ⊗ₜ x) := fun x => by
    rw [LinearMap.comp_apply, hD, AlgEquiv.toLinearMap_apply, map_sub, map_sub]
  refine ⟨Ψ.toLinearMap ∘ₗ D, ?_, ?_⟩
  · intro x
    rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_eq_zero_iff _ Ψ.injective, hD,
      Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, sub_sub, sub_eq_zero, add_comm]
  · intro p _ _ x
    have h1 : Coalgebra.comul (R := k) (x ^ p) = (Coalgebra.comul (R := k) x) ^ p := by
      simp
    have e1 : Ψ (Coalgebra.comul (R := k) x) ^ p = Ψ (Coalgebra.comul (R := k) (x ^ p)) := by
      rw [← map_pow, h1]
    have e2 : Ψ (x ⊗ₜ 1) ^ p = Ψ ((x ^ p) ⊗ₜ 1) := by
      rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
    have e3 : Ψ (1 ⊗ₜ x) ^ p = Ψ (1 ⊗ₜ (x ^ p)) := by
      rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
    rw [hL, hL, sub_pow_char, sub_pow_char, e1, e2, e3]

/-- **Lemma A.** Let `A` be a graded bialgebra domain over a field which is a polynomial algebra
on homogeneous generators `z`. If `A` has a nonzero homogeneous primitive element, then it has a
homogeneous primitive element outside the square of the augmentation ideal. One takes a nonzero
homogeneous primitive element `f` of least total degree in the coordinates `z`. If `f` were in
the square of the augmentation ideal, all its partial derivatives would vanish. In
characteristic zero `f` would be constant, hence zero. In characteristic `p` one writes
`f = ∑ bⱼ gⱼ ^ p` with `p`-independent `bⱼ`. Then the `gⱼ` are primitive and a homogeneous
component of some `gⱼ` has smaller degree. -/
theorem exists_isPrimitiveElem_not_mem_sq (h𝒜 : IsGradedBialgebra 𝒜)
    (hzw : ∀ i, z i ∈ 𝒜 (w i)) (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A))
    {f : A} (hf0 : f ≠ 0) (hf : Bialgebra.IsPrimitiveElem k f) {d : ℤ} (hfd : f ∈ 𝒜 d) :
    ∃ g : A, ∃ d' : ℤ, g ∈ 𝒜 d' ∧ Bialgebra.IsPrimitiveElem k g ∧
      g ∉ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2 := by
  set e := coordEquiv hz with he
  obtain ⟨L, hLprim, hLpow⟩ := exists_primitivity_defect hz
  suffices key : ∀ N, ∀ f : A, (e.symm f).totalDegree = N → f ≠ 0 →
      Bialgebra.IsPrimitiveElem k f → (∃ d : ℤ, f ∈ 𝒜 d) →
      ∃ g : A, ∃ d' : ℤ, g ∈ 𝒜 d' ∧ Bialgebra.IsPrimitiveElem k g ∧
        g ∉ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2 from
    key _ f rfl hf0 hf ⟨d, hfd⟩
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f hN hf0 hf hfd
  obtain ⟨d, hfd⟩ := hfd
  by_cases hf2 : f ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2
  swap
  · exact ⟨f, d, hfd, hf, hf2⟩
  have hpd := pderiv_eq_zero_of_mem_sq hz hf hf2
  set F := e.symm f with hF
  have hfF : f = e F := by rw [hF, AlgEquiv.apply_symm_apply]
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (eq_zero_of_isPrimitiveElem_of_eq_C hz hf
        (totalDegree_eq_zero_iff_eq_C.1 (hN.trans h))) hf0
    · exact h
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  swap
  · have : CharZero k := (CharP.charP_zero_iff_charZero k).1 (hp ▸ ringChar.charP k)
    exact absurd (eq_zero_of_isPrimitiveElem_of_eq_C hz hf (eq_C_of_pderiv_eq_zero hpd)) hf0
  set p := ringChar k with hpdef
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := exists_expand_of_pderiv_eq_zero p hpd
  obtain ⟨r, b, G, hb, hHG, hGs⟩ := exists_pIndependent_decomposition p H
  have hFG : F = ∑ j, b j • G j ^ p := by
    rw [hH, hHG, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← map_expand, map_frobenius_expand]
  let g : Fin r → A := fun j => e (G j)
  have hfg : f = ∑ j, b j • g j ^ p := by
    rw [hfF, hFG, map_sum]
    simp only [map_smul, map_pow, g]
  have hprim : ∀ j, Bialgebra.IsPrimitiveElem k (g j) := by
    have hsum : ∑ j, b j • L (g j) ^ p = 0 := by
      have : L f = 0 := (hLprim f).2 hf
      rw [hfg, map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hLpow p]
    intro j
    exact (hLprim _).1 (eq_zero_of_sum_smul_pow_eq_zero p hb hsum j)
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ 0 := by
    by_contra h
    push Not at h
    apply hf0
    rw [hfg]
    simp [h, zero_pow hp.ne_zero]
  obtain ⟨d', hd'⟩ : ∃ d', gradeProj 𝒜 d' (g j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hj (ext_gradeProj 𝒜 fun d' => by rw [h d', map_zero])
  have hdeg : (e.symm (gradeProj 𝒜 d' (g j))).totalDegree < N := by
    have h1 : e.symm (gradeProj 𝒜 d' (g j)) = weightedHomogeneousComponent w d' (G j) := by
      rw [AlgEquiv.symm_apply_eq]
      exact gradeProj_aeval 𝒜 hzw (G j) d'
    rw [h1]
    have h2 := totalDegree_weightedHomogeneousComponent_le (w := w) d' (G j)
    have h3 := totalDegree_le_of_support_subset (hGs j)
    have h4 : F.totalDegree = H.totalDegree * p := by rw [hH, totalDegree_expand]
    have h5 : H.totalDegree * 2 ≤ H.totalDegree * p := Nat.mul_le_mul_left _ hp.two_le
    rw [← hN] at hN0 ⊢
    omega
  exact ih _ hdeg _ rfl hd' (h𝒜.isPrimitiveElem_gradeProj (hprim j) d')
    ⟨d', gradeProj_mem 𝒜 d' (g j)⟩

end LemmaA

section Unitriangular

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A] {𝒜 : ℤ → Submodule k A}

/-- If the matrix of `G` is upper unitriangular and `A` is not reduced to the scalars, an entry
of minimal distance from the diagonal among the non-scalar entries is a nonzero primitive
element. -/
theorem exists_isPrimitiveElem_of_unitriangular (G : GradedMatrixCoefficients 𝒜)
    (hdiag : ∀ i, G.M i i = 1) (hlow : ∀ i j, j < i → G.M i j = 0)
    (hA : ∃ a : A, a ∉ Set.range (algebraMap k A)) :
    ∃ i j, G.M i j ≠ 0 ∧ Bialgebra.IsPrimitiveElem k (G.M i j) := by
  classical
  let S : Fin G.n × Fin G.n → Prop := fun p => G.M p.1 p.2 ∉ Set.range (algebraMap k A)
  have hS : ∃ g : ℕ, ∃ p, S p ∧ (p.2 : ℕ) - p.1 = g := by
    by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := hA
    apply ha
    have hle : Algebra.adjoin k (Set.range fun p : Fin G.n × Fin G.n => G.M p.1 p.2) ≤ ⊥ :=
      Algebra.adjoin_le fun _ ⟨p, hp⟩ => by
        rw [← hp]
        by_contra hc
        exact h _ p hc rfl
    rw [G.adjoin_eq_top] at hle
    have := hle (Algebra.mem_top (x := a))
    rwa [Algebra.mem_bot] at this
  obtain ⟨⟨i, j⟩, hp, hgap⟩ := Nat.find_spec hS
  have hmin : ∀ q : Fin G.n × Fin G.n, (q.2 : ℕ) - q.1 < (j : ℕ) - i → ¬ S q := fun q hq hSq =>
    Nat.find_min hS (hgap ▸ hq) ⟨q, hSq, rfl⟩
  have hconst : ∀ q : Fin G.n × Fin G.n, ¬ S q → q.1 ≠ q.2 → G.M q.1 q.2 = 0 := by
    intro q hq hne
    simp only [S, not_not] at hq
    obtain ⟨c, hc⟩ := hq
    have h1 := G.counit_apply q.1 q.2
    rw [ite_eq_right_iff.2 (fun h => absurd h hne), ← hc, Bialgebra.counit_algebraMap] at h1
    rw [← hc, h1, map_zero]
  have hij : i < j := by
    rcases lt_trichotomy i j with h | h | h
    · exact h
    · subst h
      exact absurd ⟨1, by rw [map_one, hdiag]⟩ hp
    · exact absurd ⟨0, by rw [map_zero, hlow i j h]⟩ hp
  refine ⟨i, j, fun h0 => hp ⟨0, by rw [map_zero, h0]⟩, ?_⟩
  rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, G.comul_apply,
    Fintype.sum_eq_add i j hij.ne]
  · rw [hdiag, hdiag]
  · rintro l ⟨hli, hlj⟩
    rcases lt_or_gt_of_ne hli with h | h
    · rw [hlow i l h, TensorProduct.zero_tmul]
    · rcases lt_or_gt_of_ne hlj with h' | h'
      · have hgap' : ((l : ℕ) - i) < (j : ℕ) - i := by
          have := Fin.lt_def.1 h
          have := Fin.lt_def.1 h'
          omega
        rw [hconst (i, l) (hmin (i, l) hgap') hli.symm, TensorProduct.zero_tmul]
      · rw [hlow l j h', TensorProduct.tmul_zero]

end Unitriangular

end Langlands.Algebra.GradedHopf
