import Langlands.GroupScheme.Rational.AdditiveGroupQuotient
import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.PseudoComplete
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Rational images of homomorphisms to `𝔾ₐ` or `𝔾ₘ` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

/-- Let `ψ : K ⟶ V` be a homomorphism from an affine group scheme of finite type over an
algebraically closed field to an elementary quotient `V` (`𝔾ₐ` or `𝔾ₘ`). Either every
rational point of `V` lifts to a rational point of `K`, or there is a morphism `χ` from `V`
to an affine scheme that is invariant under translation by the image of `K` on all test
points and separates the rational cosets of that image. -/
def StabilizerImageDichotomyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (K V : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom K.X.hom] [LocallyOfFiniteType K.X.hom] (ψ : K ⟶ V),
    SplitSolvable.IsElementaryQuotient V →
      (∀ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X,
          ∃ s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X, s ≫ ψ.hom.hom = v) ∨
        ∃ (W : Over (Spec (CommRingCat.of k))) (χ : V.X ⟶ W),
          IsAffine W.left ∧
            (∀ (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) (s : T ⟶ K.X),
              (v * (s ≫ ψ.hom.hom)) ≫ χ = v ≫ χ) ∧
            ∀ v w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X, v ≫ χ = w ≫ χ →
              ∃ s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X,
                v * (s ≫ ψ.hom.hom) = w

namespace StabilizerImageDichotomy

open Polynomial

/-! ### Commutative algebra over an algebraically closed field -/

section Algebra

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]

/-- Hilbert's Nullstellensatz: every maximal ideal of a finite-type algebra over an
algebraically closed field is the kernel of a `k`-point. -/
theorem exists_algHom_of_isMaximal [IsAlgClosed k] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : ∃ φ : A →ₐ[k] k, ∀ a, φ a = 0 ↔ a ∈ m := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let ψ : (A ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ k m), fun a => ?_⟩
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.eq_zero_iff_mem]
  exact map_eq_zero_iff ψ (ψ : A ⧸ m →+* k).injective

/-- An element vanishing at every `k`-point is nilpotent. -/
theorem isNilpotent_of_forall_algHom [IsAlgClosed k] [Algebra.FiniteType k A] {a : A}
    (h : ∀ φ : A →ₐ[k] k, φ a = 0) : IsNilpotent a := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have ha : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_of_isMaximal (k := k) m
    exact (hφ a).1 (h φ)
  rw [← Ideal.radical_eq_jacobson] at ha
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, by simpa using hn⟩

/-- The closed point `X - c` of the affine line. -/
def linePoint (c : k) : PrimeSpectrum (Polynomial k) :=
  ⟨RingHom.ker (Polynomial.evalRingHom c), RingHom.ker_isPrime _⟩

/-- A constructible subset of the affine line contains finitely many or cofinitely many of the
points `X - c`. -/
theorem finite_or_cofinite_preimage {s : Set (PrimeSpectrum (Polynomial k))}
    (hs : Topology.IsConstructible s) :
    (linePoint ⁻¹' s).Finite ∨ (linePoint ⁻¹' s)ᶜ.Finite := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).1 hU.isClosed_compl
    by_cases h : ∃ g ∈ I, g ≠ 0
    · obtain ⟨g, hg, hg0⟩ := h
      right
      refine (Polynomial.finite_setOfPred_isRoot hg0).subset fun c hc => ?_
      have hc' : linePoint c ∈ Uᶜ := hc
      rw [hI] at hc'
      have := (PrimeSpectrum.mem_zeroLocus _ _).1 hc' hg
      simpa [linePoint, RingHom.mem_ker] using this
    · left
      push Not at h
      refine Set.finite_empty.subset fun c hc => ?_
      have hc' : linePoint c ∈ Uᶜ := by
        rw [hI, PrimeSpectrum.mem_zeroLocus]
        intro g hg
        rw [h g hg]
        exact Ideal.zero_mem _
      exact hc' hc
  | union s _ t _ hs ht =>
    rw [Set.preimage_union]
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact Or.inl (hs.union ht)
    · exact Or.inr (ht.subset (Set.compl_subset_compl.2 Set.subset_union_right))
    · exact Or.inr (hs.subset (Set.compl_subset_compl.2 Set.subset_union_left))
    · exact Or.inr (hs.subset (Set.compl_subset_compl.2 Set.subset_union_left))
  | compl s _ hs =>
    rw [Set.preimage_compl, compl_compl]
    exact hs.symm

/-- The values of an element at the `k`-points. -/
def values (a : A) : Set k := {c | ∃ φ : A →ₐ[k] k, φ a = c}

/-- Chevalley's theorem on the affine line: the values of an element of a finite-type algebra
over an algebraically closed field at the `k`-points form a finite or a cofinite set. -/
theorem values_finite_or_cofinite [IsAlgClosed k] [Algebra.FiniteType k A] (a : A) :
    (values (k := k) a).Finite ∨ (values (k := k) a)ᶜ.Finite := by
  let f : Polynomial k →+* A := (Polynomial.aeval (R := k) a).toRingHom
  have hfC : f.comp Polynomial.C = algebraMap k A := by
    ext c
    simp [f]
  have hf : f.FinitePresentation := by
    rw [← RingHom.FinitePresentation.of_finiteType]
    refine RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C) ?_
    rw [hfC, RingHom.finiteType_algebraMap]
    infer_instance
  have heq : values a = linePoint ⁻¹' Set.range (PrimeSpectrum.comap f) := by
    ext c
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨⟨RingHom.ker (φ : A →+* k), RingHom.ker_isPrime _⟩, ?_⟩
      have hφf : (φ : A →+* k).comp f = Polynomial.evalRingHom (φ a) := by
        apply Polynomial.ringHom_ext
        · intro c
          simp [f]
        · simp [f]
      ext1
      rw [PrimeSpectrum.comap_asIdeal, RingHom.comap_ker, hφf]
      rfl
    · rintro ⟨q, hq⟩
      have hX : Polynomial.X - Polynomial.C c ∈ (linePoint c).asIdeal := by
        simp [linePoint, RingHom.mem_ker]
      rw [← hq, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hX
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
      obtain ⟨φ, hφ⟩ := exists_algHom_of_isMaximal (k := k) m
      refine ⟨φ, ?_⟩
      have h0 := (hφ _).2 (hle hX)
      simp only [f, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, aeval_C,
        AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h0
      exact sub_eq_zero.1 h0
  rw [heq]
  exact finite_or_cofinite_preimage (PrimeSpectrum.isConstructible_range_comap hf)

omit [Algebra k A] in
/-- A nilpotent element killed by every power of the exponential characteristic: in
characteristic zero this needs the separate hypothesis that the element is zero. -/
theorem exists_pow_expChar_pow_eq_zero (q : ℕ) [hq : ExpChar k q] {x : A}
    (hx : IsNilpotent x) (h0 : CharZero k → x = 0) : ∃ e : ℕ, x ^ q ^ e = 0 := by
  cases hq with
  | zero => exact ⟨0, by simpa using h0 inferInstance⟩
  | prime hp =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le hn⟩

/-- The key tensor identity behind Cartier's theorem in characteristic zero. If `a`, `b`
satisfy `a ^ M = b ^ M = 0` and `(a + c * b) ^ M = 0` with `M ≥ 2`, then
`M * a ^ (M - 1) * c ^ (M - 1) * b ^ (M - 1) = 0`. -/
theorem nat_mul_pow_mul_pow_eq_zero {R : Type*} [CommRing R] {a b c : R} {M : ℕ}
    (hM : 2 ≤ M) (ha : a ^ M = 0) (hb : b ^ M = 0) (habc : (a + c * b) ^ M = 0) :
    (M : R) * a ^ (M - 1) * c ^ (M - 1) * b ^ (M - 1) = 0 := by
  have key : a ^ (M - 2) * (a + c * b) ^ M = (M : R) * a ^ (M - 1) * c ^ (M - 1) * b ^ (M - 1) := by
    rw [add_pow, Finset.mul_sum, Finset.sum_eq_single 1]
    · rw [Nat.choose_one_right, pow_one, mul_pow]
      have h1 : M - 2 + 1 = M - 1 := by omega
      calc a ^ (M - 2) * (a * (c ^ (M - 1) * b ^ (M - 1)) * (M : R))
          = (M : R) * (a ^ (M - 2) * a) * c ^ (M - 1) * b ^ (M - 1) := by ring
        _ = (M : R) * a ^ (M - 1) * c ^ (M - 1) * b ^ (M - 1) := by
          rw [← pow_succ, h1]
    · intro i hi hi1
      rw [Finset.mem_range] at hi
      rcases Nat.lt_or_ge i 1 with h | h
      · obtain rfl : i = 0 := by omega
        rw [Nat.sub_zero, mul_pow, hb, mul_zero, mul_zero, zero_mul, mul_zero]
      · have : a ^ (M - 2) * a ^ i = 0 := by
          rw [← pow_add]
          exact pow_eq_zero_of_le (by omega) ha
        calc a ^ (M - 2) * (a ^ i * (c * b) ^ (M - i) * (M.choose i : R))
            = (a ^ (M - 2) * a ^ i) * ((c * b) ^ (M - i) * (M.choose i : R)) := by ring
          _ = 0 := by rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  rw [← key, habc, mul_zero]

/-- Cartier's theorem for a single coordinate in characteristic zero: a nilpotent element whose
comultiplication has the shape `n ⊗ 1 + c (1 ⊗ n)` with `c` a unit is zero. -/
theorem eq_zero_of_comul [CharZero k] (δ : A →+* TensorProduct k A A) {n c : A}
    (hc : IsUnit c) (hδ : δ n = n ⊗ₜ[k] 1 + (c ⊗ₜ[k] 1) * ((1 : A) ⊗ₜ[k] n))
    (hn : IsNilpotent n) : n = 0 := by
  obtain ⟨M, hM⟩ := hn
  induction M with
  | zero =>
    have : (1 : A) = 0 := by simpa using hM
    rw [← mul_one n, this, mul_zero]
  | succ M ih =>
    rcases Nat.lt_or_ge M 1 with h | h
    · obtain rfl : M = 0 := by omega
      simpa using hM
    apply ih
    have ha : (n ⊗ₜ[k] (1 : A)) ^ (M + 1) = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, hM, one_pow, TensorProduct.zero_tmul]
    have hb : ((1 : A) ⊗ₜ[k] n) ^ (M + 1) = 0 := by
      rw [Algebra.TensorProduct.tmul_pow, hM, one_pow, TensorProduct.tmul_zero]
    have habc : (n ⊗ₜ[k] (1 : A) + (c ⊗ₜ[k] 1) * ((1 : A) ⊗ₜ[k] n)) ^ (M + 1) = 0 := by
      rw [← hδ, ← map_pow, hM, map_zero]
    have h2 := nat_mul_pow_mul_pow_eq_zero (by omega) ha hb habc
    simp only [Nat.add_sub_cancel] at h2
    have hcu : IsUnit ((c ⊗ₜ[k] (1 : A)) ^ M) :=
      (hc.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A A)).pow M
    have h3 : (M + 1 : TensorProduct k A A) * ((n ^ M) ⊗ₜ[k] (n ^ M)) = 0 := by
      have : (M + 1 : TensorProduct k A A) * ((n ^ M) ⊗ₜ[k] (n ^ M)) *
          (c ⊗ₜ[k] (1 : A)) ^ M = 0 := by
        rw [← h2]
        simp only [Algebra.TensorProduct.tmul_pow, one_pow]
        rw [show (n ^ M) ⊗ₜ[k] (n ^ M) = ((n ^ M) ⊗ₜ[k] (1 : A)) * ((1 : A) ⊗ₜ[k] (n ^ M)) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
        push_cast
        ring
      exact (hcu.mul_left_eq_zero).1 this
    have h4 : (n ^ M) ⊗ₜ[k] (n ^ M) = 0 := by
      have hM0 : ((M + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero M)
      have : ((M + 1 : ℕ) : k) • ((n ^ M) ⊗ₜ[k] (n ^ M)) = 0 := by
        rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
        push_cast
        exact h3
      exact (smul_eq_zero.1 this).resolve_left hM0
    by_contra hne
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero k hne
    have h5 := congrArg (TensorProduct.lift (LinearMap.lsmul k A ∘ₗ g).flip) h4
    rw [TensorProduct.lift.tmul, map_zero] at h5
    simp only [LinearMap.flip_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lsmul_apply] at h5
    exact hne ((smul_eq_zero.1 h5).resolve_left hg)

/-- The additivity defect `F (X₀ + X₁) - F X₀ - F X₁` of a polynomial, as a polynomial in two
variables. -/
def addDefect (F : Polynomial k) : MvPolynomial (Fin 2) k :=
  Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.X 1) F -
    Polynomial.aeval (MvPolynomial.X 0) F - Polynomial.aeval (MvPolynomial.X 1) F

theorem eval₂Hom_addDefect (F : Polynomial k) {R : Type*} [CommRing R] (g : k →+* R)
    (x : Fin 2 → R) :
    MvPolynomial.eval₂Hom g x (addDefect F) =
      F.eval₂ g (x 0 + x 1) - F.eval₂ g (x 0) - F.eval₂ g (x 1) := by
  simp only [addDefect, map_sub, Polynomial.aeval_def, Polynomial.hom_eval₂, map_add,
    MvPolynomial.eval₂Hom_X', MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_comp_C]

/-- A polynomial that is additive on an infinite field is additive in every commutative ring
receiving a ring map from the field. -/
theorem eval₂_add_of_eval_add [Infinite k] (F : Polynomial k)
    (hF : ∀ a b : k, F.eval (a + b) = F.eval a + F.eval b)
    {R : Type*} [CommRing R] (g : k →+* R) (a b : R) :
    F.eval₂ g (a + b) = F.eval₂ g a + F.eval₂ g b := by
  have hG : addDefect F = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, MvPolynomial.eval, eval₂Hom_addDefect F (RingHom.id k) x]
    simp only [Polynomial.eval₂_id]
    rw [hF]
    ring
  have := eval₂Hom_addDefect F g ![a, b]
  rw [hG, map_zero] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [eq_comm, sub_sub, sub_eq_zero] at this
  exact this

/-- The vanishing polynomial of a finite additive subgroup of a field is additive on the
field. -/
theorem eval_add_prod_sub (Λ : AddSubgroup k) [Fintype Λ] (a b : k) :
    (∏ l : Λ, (X - C (l : k))).eval (a + b) =
      (∏ l : Λ, (X - C (l : k))).eval a + (∏ l : Λ, (X - C (l : k))).eval b := by
  set P : Polynomial k := ∏ l : Λ, (X - C (l : k)) with hP
  have hmonic : P.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  have hdeg : P.natDegree = Fintype.card Λ := by
    rw [hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _]
    simp
  have hroot : ∀ l : Λ, P.eval (l : k) = 0 := by
    intro l
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  have htrans : ∀ l : Λ, ∀ x : k, P.eval (x + l) = P.eval x := by
    intro l x
    rw [hP, eval_prod, eval_prod]
    rw [← Equiv.prod_comp (Equiv.addRight l)]
    refine Finset.prod_congr rfl fun ν _ => ?_
    simp only [eval_sub, eval_X, eval_C, Equiv.coe_addRight, AddSubgroup.coe_add]
    ring
  have hcard : 0 < Fintype.card Λ := Fintype.card_pos
  let R : Polynomial k := P.comp (X + C a) - P - C (P.eval a)
  have hPdeg : P.degree = (Fintype.card Λ : WithBot ℕ) := by
    rw [degree_eq_natDegree hmonic.ne_zero, hdeg]
  have h1 : (P.comp (X + C a)).Monic := hmonic.comp_X_add_C a
  have hdeg1 : (P.comp (X + C a)).degree = P.degree := by
    rw [degree_eq_natDegree h1.ne_zero, degree_eq_natDegree hmonic.ne_zero, natDegree_comp,
      natDegree_X_add_C, mul_one]
  have h3 : (P.comp (X + C a) - P).degree < Fintype.card Λ := by
    rw [← hPdeg, ← hdeg1]
    exact degree_sub_lt_left hdeg1 h1.ne_zero (by rw [h1.leadingCoeff, hmonic.leadingCoeff])
  have hRdeg : R.degree < Fintype.card Λ := by
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt h3 ?_)
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hcard)
  have heval : ∀ l : Λ, R.eval (l : k) = 0 := by
    intro l
    simp only [R, eval_sub, eval_comp, eval_add, eval_X, eval_C, hroot, sub_zero]
    rw [add_comm, htrans]
    ring
  have hR : R = 0 := by
    by_contra hR0
    exact hR0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero R
      (f := fun l : Λ => (l : k)) Subtype.val_injective heval
      ((natDegree_lt_iff_degree_lt hR0).2 hRdeg))
  have := congrArg (Polynomial.eval b) hR
  simp only [R, eval_sub, eval_comp, eval_add, eval_X, eval_C, eval_zero] at this
  rw [add_comm a b]
  linear_combination this

/-- Cartier's theorem for an additive polynomial in a primitive element in characteristic
zero: if the value of an additive polynomial at a primitive element is nilpotent, it is zero. -/
theorem aeval_eq_zero_of_primitive [CharZero k] (δ : A →ₐ[k] A ⊗[k] A) {u : A}
    (hu : δ u = u ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u) (P : Polynomial k)
    (hP : ∀ a b : k, P.eval (a + b) = P.eval a + P.eval b) (hn : IsNilpotent (aeval u P)) :
    aeval u P = 0 := by
  refine eq_zero_of_comul δ.toRingHom isUnit_one ?_ hn
  rw [← Algebra.TensorProduct.one_def, _root_.one_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    ← Polynomial.aeval_algHom_apply, hu, aeval_def, eval₂_add_of_eval_add P hP, ← aeval_def,
    ← aeval_def]
  congr 1
  · exact Polynomial.aeval_algHom_apply
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) u P
  · exact Polynomial.aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) u P

/-- Cartier's theorem for a group-like unit in characteristic zero: if `u ^ m - 1` is nilpotent
for a group-like unit `u`, it is zero. -/
theorem pow_sub_one_eq_zero_of_grouplike [CharZero k] (δ : A →ₐ[k] A ⊗[k] A) {u : A}
    (hu : IsUnit u) (hδ : δ u = (u ⊗ₜ[k] 1) * (1 ⊗ₜ[k] u)) (m : ℕ)
    (hn : IsNilpotent (u ^ m - 1)) : u ^ m - 1 = 0 := by
  refine eq_zero_of_comul δ.toRingHom (c := u ^ m) (hu.pow _) ?_ hn
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_pow, map_one, hδ]
  have e1 : ∀ x : A, x ⊗ₜ[k] (1 : A) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) x := fun _ => rfl
  have e2 : ∀ x : A, (1 : A) ⊗ₜ[k] x =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) x := fun _ => rfl
  simp only [e1, e2, map_sub, map_pow, map_one]
  ring

/-- A subgroup with finite complement in a group is the whole group as soon as it is
infinite. -/
@[to_additive add_mem_of_compl_finite /-- An additive subgroup with finite complement is the whole group as soon as it
is infinite. -/]
theorem mem_of_compl_finite {G : Type*} [Group G] (H : Subgroup G)
    (hH : ¬ (H : Set G).Finite) (hc : (H : Set G)ᶜ.Finite) (g : G) : g ∈ H := by
  by_contra hg
  apply hH
  refine (hc.image fun x => g * x⁻¹).subset fun l hl => ⟨l⁻¹ * g, fun h => hg ?_, ?_⟩
  · simpa using H.mul_mem hl h
  · simp

/-- In exponential characteristic `q`, the `q ^ e`-th power map of a field is injective at `1`. -/
theorem eq_one_of_pow_expChar_pow_eq_one (q : ℕ) [ExpChar k q] {z : k} (e : ℕ)
    (h : z ^ q ^ e = 1) : z = 1 := by
  have h1 : (z - 1) ^ q ^ e = 0 := by rw [sub_pow_expChar_pow, one_pow, h, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ (expChar_pos k q).ne')).1 h1)

end Algebra

/-! ### Global functions and points of schemes over the field -/

section Points

variable {k : Type u} [Field k]

/-- The rational base point: `Spec k` as a scheme over itself. -/
abbrev pt (k : Type u) [Field k] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (𝟙 (Spec (CommRingCat.of k)))

theorem constants_apply (T : Over (Spec (CommRingCat.of k))) (c : k) :
    RelativeRoot.AdditiveGroupQuotient.structureMap T c = T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := rfl

/-- Morphisms over `Spec k` preserve constants. -/
theorem appTop_constants {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T) (c : k) :
    b.left.appTop (RelativeRoot.AdditiveGroupQuotient.structureMap T c) = RelativeRoot.AdditiveGroupQuotient.structureMap T' c := by
  rw [constants_apply, constants_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Over.w b]

theorem ΓSpecIso_constants_pt (c : k) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom (RelativeRoot.AdditiveGroupQuotient.structureMap (pt k) c) = c := by
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k)))
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) = c
  rw [Scheme.Hom.id_appTop, CommRingCat.id_apply, Iso.inv_hom_id_apply]

theorem ΓSpecIso_constants_algebraSpec (B : Type u) [CommRing B] [Algebra k B] (c : k) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom (RelativeRoot.AdditiveGroupQuotient.structureMap (PseudoComplete.algebraSpec k B) c) =
      algebraMap k B c := by
  have e := congrArg (fun g => CommRingCat.Hom.hom g ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k B)))
  refine e.trans ?_
  simp

theorem ΓSpecIso_isoSpec_inv_appTop (Y : Scheme.{u}) [IsAffine Y] (x : Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso Γ(Y, ⊤)).hom (Y.isoSpec.inv.appTop x) = x := by
  have h := congrArg (fun f => Scheme.Hom.appTop f x) (Scheme.toSpecΓ_isoSpec_inv Y)
  simpa only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, CommRingCat.comp_apply,
    Scheme.Hom.id_appTop, CommRingCat.id_apply] using h

/-- The finite type property of a scheme over `Spec k`, on global functions. -/
theorem finiteType_constants (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : (RelativeRoot.AdditiveGroupQuotient.structureMap X).FiniteType := by
  have h : X.hom.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 inferInstance
  exact h.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective)

theorem ΓSpecIso_specMap_isoSpec_inv_appTop (Y : Scheme.{u}) [IsAffine Y] {B : Type u}
    [CommRing B] (φ : Γ(Y, ⊤) →+* B) (x : Γ(Y, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      ((Spec.map (CommRingCat.ofHom φ) ≫ Y.isoSpec.inv).appTop x) = φ x := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  exact congrArg φ (ΓSpecIso_isoSpec_inv_appTop Y x)

theorem specMap_isoSpec_inv_comp (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    {B : Type u} [CommRing B] [Algebra k B] (φ : Γ(X.left, ⊤) →+* B)
    (hφ : ∀ c, φ (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = algebraMap k B c) :
    (Spec.map (CommRingCat.ofHom φ) ≫ X.left.isoSpec.inv) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact hφ c

/-- The `B`-valued point of an affine scheme over `Spec k` given by a ring map on global
functions compatible with the constants. -/
def pointOf (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] {B : Type u} [CommRing B]
    [Algebra k B] (φ : Γ(X.left, ⊤) →+* B) (hφ : ∀ c, φ (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = algebraMap k B c) :
    PseudoComplete.algebraSpec k B ⟶ X :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ X.left.isoSpec.inv)
    (specMap_isoSpec_inv_comp X φ hφ)

theorem ΓSpecIso_pointOf_appTop (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    {B : Type u} [CommRing B] [Algebra k B] (φ : Γ(X.left, ⊤) →+* B)
    (hφ : ∀ c, φ (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = algebraMap k B c) (x : Γ(X.left, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((pointOf X φ hφ).left.appTop x) = φ x :=
  ΓSpecIso_specMap_isoSpec_inv_appTop X.left φ x

/-- Global functions evaluated at a `B`-valued point. -/
def pointHom {X : Over (Spec (CommRingCat.of k))} {B : Type u} [CommRing B] [Algebra k B]
    (t : PseudoComplete.algebraSpec k B ⟶ X) : Γ(X.left, ⊤) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp t.left.appTop.hom

theorem pointHom_apply {X : Over (Spec (CommRingCat.of k))} {B : Type u} [CommRing B]
    [Algebra k B] (t : PseudoComplete.algebraSpec k B ⟶ X) (x : Γ(X.left, ⊤)) :
    pointHom t x = (Scheme.ΓSpecIso (CommRingCat.of B)).hom (t.left.appTop x) := rfl

theorem pointHom_constants {X : Over (Spec (CommRingCat.of k))} {B : Type u} [CommRing B]
    [Algebra k B] (t : PseudoComplete.algebraSpec k B ⟶ X) (c : k) :
    pointHom t (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = algebraMap k B c := by
  rw [pointHom_apply, appTop_constants, ΓSpecIso_constants_algebraSpec]

/-- Global functions evaluated at a rational point. -/
def ratHom {X : Over (Spec (CommRingCat.of k))} (s : pt k ⟶ X) : Γ(X.left, ⊤) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp s.left.appTop.hom

theorem ratHom_apply {X : Over (Spec (CommRingCat.of k))} (s : pt k ⟶ X) (x : Γ(X.left, ⊤)) :
    ratHom s x = (Scheme.ΓSpecIso (CommRingCat.of k)).hom (s.left.appTop x) := rfl

theorem ratHom_constants {X : Over (Spec (CommRingCat.of k))} (s : pt k ⟶ X) (c : k) :
    ratHom s (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = c := by
  rw [ratHom_apply, appTop_constants, ΓSpecIso_constants_pt]

/-- The rational point of an affine scheme over `Spec k` given by a `k`-valued ring map on
global functions compatible with the constants. -/
def rationalPoint (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    (φ : Γ(X.left, ⊤) →+* k) (hφ : ∀ c, φ (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = c) : pt k ⟶ X :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ X.left.isoSpec.inv)
    ((specMap_isoSpec_inv_comp X φ hφ).trans (by simp))

theorem ratHom_rationalPoint (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    (φ : Γ(X.left, ⊤) →+* k) (hφ : ∀ c, φ (RelativeRoot.AdditiveGroupQuotient.structureMap X c) = c) :
    ratHom (rationalPoint X φ hφ) = φ :=
  RingHom.ext fun x => ΓSpecIso_specMap_isoSpec_inv_appTop X.left φ x

/-- The two points of an affine scheme with values in the tensor square of its global
functions. -/
theorem exists_tensor_points (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    [Algebra k Γ(X.left, ⊤)] (hX : ∀ c, algebraMap k Γ(X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap X c) :
    ∃ t₁ t₂ : PseudoComplete.algebraSpec k (Γ(X.left, ⊤) ⊗[k] Γ(X.left, ⊤)) ⟶ X,
      (∀ x, pointHom t₁ x = x ⊗ₜ[k] 1) ∧ (∀ x, pointHom t₂ x = 1 ⊗ₜ[k] x) := by
  refine ⟨pointOf X (Algebra.TensorProduct.includeLeft : _ →ₐ[k] _).toRingHom
      (fun c => by rw [← hX]; exact AlgHom.commutes _ c),
    pointOf X (Algebra.TensorProduct.includeRight : _ →ₐ[k] _).toRingHom
      (fun c => by rw [← hX]; exact AlgHom.commutes _ c), fun x => ?_, fun x => ?_⟩
  · exact ΓSpecIso_pointOf_appTop X _ _ x
  · exact ΓSpecIso_pointOf_appTop X _ _ x

/-- The comultiplication on the global functions of an affine group scheme over `Spec k`: the
`k`-algebra map given by the product of the two tautological points with values in the tensor
square of the global functions. -/
theorem exists_comul (K : GroupScheme (Spec (CommRingCat.of k))) [IsAffine K.X.left]
    [Algebra k Γ(K.X.left, ⊤)] (hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c) :
    ∃ (t₁ t₂ : PseudoComplete.algebraSpec k (Γ(K.X.left, ⊤) ⊗[k] Γ(K.X.left, ⊤)) ⟶ K.X)
      (δ : Γ(K.X.left, ⊤) →ₐ[k] Γ(K.X.left, ⊤) ⊗[k] Γ(K.X.left, ⊤)),
      (∀ x, pointHom t₁ x = x ⊗ₜ[k] 1) ∧ (∀ x, pointHom t₂ x = 1 ⊗ₜ[k] x) ∧
        ∀ x, δ x = pointHom (t₁ * t₂) x := by
  obtain ⟨t₁, t₂, h₁, h₂⟩ := exists_tensor_points K.X hA
  exact ⟨t₁, t₂, AlgHom.mk (pointHom (t₁ * t₂)) fun c =>
    (congrArg (pointHom (t₁ * t₂)) (hA c)).trans (pointHom_constants _ c), h₁, h₂, fun _ => rfl⟩

/-- Polynomials in a global function commute with pullback along morphisms over `Spec k`. -/
theorem appTop_eval₂_constants {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T)
    (F : Polynomial k) (x : Γ(T.left, ⊤)) :
    b.left.appTop (F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap T) x) = F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap T') (b.left.appTop x) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  ext c
  exact appTop_constants b c

theorem ΓSpecIso_eval₂_constants_pt (F : Polynomial k) (y : Γ((pt k).left, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom (F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap (pt k)) y) =
      F.eval ((Scheme.ΓSpecIso (CommRingCat.of k)).hom y) := by
  rw [Polynomial.hom_eval₂]
  show _ = F.eval₂ (RingHom.id k) _
  congr 1
  ext c
  exact ΓSpecIso_constants_pt c

/-- A rational point as a `k`-algebra map on global functions. -/
def ratAlgHom {X : Over (Spec (CommRingCat.of k))} [Algebra k Γ(X.left, ⊤)]
    (hX : ∀ c, algebraMap k Γ(X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap X c) (s : pt k ⟶ X) :
    Γ(X.left, ⊤) →ₐ[k] k :=
  AlgHom.mk (ratHom s) fun c => (congrArg (ratHom s) (hX c)).trans (ratHom_constants s c)

end Points

/-! ### Coordinates on `𝔾ₐ` and `𝔾ₘ` -/

section Coordinates

variable {k : Type u} [Field k]

/-- A natural additive coordinate on a group scheme over `Spec k`: its points are identified
with global functions, additively in the group law and naturally in the test scheme. -/
structure AddCoordinate (V : GroupScheme (Spec (CommRingCat.of k))) where
  /-- The coordinate of a point. -/
  coord : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃ Γ(T.left, ⊤)
  coord_mul : ∀ (T : Over (Spec (CommRingCat.of k))) (v w : T ⟶ V.X),
    coord T (v * w) = coord T v + coord T w
  coord_comp : ∀ {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T) (v : T ⟶ V.X),
    coord T' (b ≫ v) = b.left.appTop (coord T v)

/-- A natural multiplicative coordinate on a group scheme over `Spec k`: its points are
identified with global units, multiplicatively and naturally in the test scheme. -/
structure MulCoordinate (V : GroupScheme (Spec (CommRingCat.of k))) where
  /-- The coordinate of a point. -/
  coord : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃* (Γ(T.left, ⊤))ˣ
  coord_comp : ∀ {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T) (v : T ⟶ V.X),
    coord T' (b ≫ v) = Units.map b.left.appTop.hom.toMonoidHom (coord T v)

variable {V : GroupScheme (Spec (CommRingCat.of k))}

/-- The coordinate of a one-dimensional vector group. -/
def AddCoordinate.ofVectorGroup (h : RelativeRoot.IsVectorGroupOfDimension V 1) :
    AddCoordinate V where
  coord T := (h.choose T).toEquiv.trans
    (Multiplicative.toAdd.trans (Equiv.funUnique (Fin 1) Γ(T.left, ⊤)))
  coord_mul T v w := by
    simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul,
      toAdd_mul, Equiv.funUnique_apply, Pi.add_apply]
  coord_comp b v := by
    simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      Equiv.funUnique_apply]
    exact congrFun (h.choose_spec _ _ b v) _

/-- The coordinate of a group scheme isomorphic to `𝔾ₘ`. -/
def MulCoordinate.ofIso (f : V ≅ (Gm (Spec (CommRingCat.of k))).toGrp) : MulCoordinate V where
  coord T := ((yonedaGrp.mapIso f).app (op T)).groupIsoToMulEquiv.trans
    (Gm.pointsEquiv (Spec (CommRingCat.of k)) T)
  coord_comp b v := by
    change Gm.pointsEquiv _ _ ((b ≫ v) ≫ f.hom.hom.hom) =
      Units.map _ (Gm.pointsEquiv _ _ (v ≫ f.hom.hom.hom))
    rw [Category.assoc, Gm.pointsEquiv_naturality]

namespace AddCoordinate

variable (C : AddCoordinate V)

theorem coord_one (T : Over (Spec (CommRingCat.of k))) : C.coord T 1 = 0 := by
  have h := C.coord_mul T 1 1
  rw [_root_.mul_one] at h
  exact left_eq_add.1 h

theorem coord_inv (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) :
    C.coord T v⁻¹ = -C.coord T v := by
  have h := C.coord_mul T v⁻¹ v
  rw [inv_mul_cancel, coord_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The coordinate of a rational point, as an element of the field. -/
def rat (v : pt k ⟶ V.X) : k := (Scheme.ΓSpecIso (CommRingCat.of k)).hom (C.coord (pt k) v)

theorem rat_injective : Function.Injective C.rat := fun _ _ h =>
  (C.coord _).injective ((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective h)

theorem rat_mul (v w : pt k ⟶ V.X) : C.rat (v * w) = C.rat v + C.rat w := by
  rw [rat, C.coord_mul, map_add]
  rfl

theorem rat_one : C.rat 1 = 0 := by
  rw [rat, C.coord_one, map_zero]

theorem rat_inv (v : pt k ⟶ V.X) : C.rat v⁻¹ = -C.rat v := by
  rw [rat, C.coord_inv, map_neg]
  rfl

end AddCoordinate

namespace MulCoordinate

variable (C : MulCoordinate V)

/-- The coordinate of a rational point, as a unit of the field. -/
def rat (v : pt k ⟶ V.X) : kˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom (C.coord (pt k) v)

theorem val_rat (v : pt k ⟶ V.X) :
    (C.rat v : k) = (Scheme.ΓSpecIso (CommRingCat.of k)).hom (C.coord (pt k) v).val := rfl

theorem rat_injective : Function.Injective C.rat := fun _ _ h =>
  (C.coord _).injective (Units.ext
    ((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective (congrArg Units.val h)))

theorem rat_mul (v w : pt k ⟶ V.X) : C.rat (v * w) = C.rat v * C.rat w := by
  rw [rat, map_mul, map_mul]
  rfl

theorem rat_one : C.rat 1 = 1 := by
  rw [rat, map_one, map_one]

theorem rat_inv (v : pt k ⟶ V.X) : C.rat v⁻¹ = (C.rat v)⁻¹ := by
  rw [rat, map_inv, map_inv]
  rfl

theorem rat_pow (v : pt k ⟶ V.X) (n : ℕ) : C.rat (v ^ n) = C.rat v ^ n := by
  rw [rat, map_pow, map_pow]
  rfl

end MulCoordinate

/-! ### Rational images of a homomorphism in coordinates -/

variable {K : GroupScheme (Spec (CommRingCat.of k))}

namespace AddCoordinate

variable (C : AddCoordinate V)

theorem rat_comp {X : Over (Spec (CommRingCat.of k))} (g : X ⟶ V.X) (s : pt k ⟶ X) :
    C.rat (s ≫ g) = ratHom s (C.coord X g) := by
  rw [rat, C.coord_comp]
  rfl

theorem pointHom_coord {X : Over (Spec (CommRingCat.of k))} (g : X ⟶ V.X) {B : Type u}
    [CommRing B] [Algebra k B] (t : PseudoComplete.algebraSpec k B ⟶ X) :
    pointHom t (C.coord X g) = (Scheme.ΓSpecIso (CommRingCat.of B)).hom (C.coord _ (t ≫ g)) := by
  rw [C.coord_comp]
  rfl

theorem pointHom_mul (ψ : K ⟶ V) {B : Type u} [CommRing B] [Algebra k B]
    (t₁ t₂ : PseudoComplete.algebraSpec k B ⟶ K.X) :
    pointHom (t₁ * t₂) (C.coord K.X ψ.hom.hom) =
      pointHom t₁ (C.coord K.X ψ.hom.hom) + pointHom t₂ (C.coord K.X ψ.hom.hom) := by
  rw [C.pointHom_coord, C.pointHom_coord, C.pointHom_coord, MonObj.mul_comp, C.coord_mul]
  exact map_add (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom _ _

/-- The coordinate of a homomorphism to `V` is primitive for the comultiplication. -/
theorem exists_comul (ψ : K ⟶ V) [IsAffine K.X.left] [Algebra k Γ(K.X.left, ⊤)]
    (hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c) :
    ∃ δ : Γ(K.X.left, ⊤) →ₐ[k] Γ(K.X.left, ⊤) ⊗[k] Γ(K.X.left, ⊤),
      δ (C.coord K.X ψ.hom.hom) =
        C.coord K.X ψ.hom.hom ⊗ₜ[k] 1 + 1 ⊗ₜ[k] C.coord K.X ψ.hom.hom := by
  obtain ⟨t₁, t₂, δ, h₁, h₂, hδ⟩ := StabilizerImageDichotomy.exists_comul K hA
  exact ⟨δ, by rw [hδ, C.pointHom_mul ψ, h₁, h₂]⟩

/-- The coordinates of the rational points of `V` in the image of `ψ`. -/
def image (ψ : K ⟶ V) : AddSubgroup k where
  carrier := {c | ∃ s : pt k ⟶ K.X, C.rat (s ≫ ψ.hom.hom) = c}
  zero_mem' := ⟨1, by rw [MonObj.one_comp, C.rat_one]⟩
  add_mem' := by
    rintro _ _ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩
    exact ⟨s₁ * s₂, by rw [MonObj.mul_comp, C.rat_mul]⟩
  neg_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨s⁻¹, by rw [GrpObj.inv_comp, C.rat_inv]⟩

theorem mem_image (ψ : K ⟶ V) {c : k} :
    c ∈ C.image ψ ↔ ∃ s : pt k ⟶ K.X, C.rat (s ≫ ψ.hom.hom) = c := Iff.rfl

/-- The rational image of `ψ` consists of the values of its coordinate at the `k`-points. -/
theorem coe_image (ψ : K ⟶ V) [IsAffine K.X.left] [Algebra k Γ(K.X.left, ⊤)]
    (hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c) :
    (C.image ψ : Set k) = values (k := k) (C.coord K.X ψ.hom.hom) := by
  ext c
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨ratAlgHom hA s, (C.rat_comp _ s).symm⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨rationalPoint K.X φ.toRingHom fun c => ?_, ?_⟩
    · rw [← hA]
      exact φ.commutes c
    · rw [C.rat_comp, ratHom_rationalPoint]
      rfl

/-- A polynomial with coefficients in `k` applied to the coordinate defines an endomorphism of
the scheme underlying `V`. -/
theorem exists_polynomial_map (F : Polynomial k) :
    ∃ χ : V.X ⟶ V.X,
      (∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ V.X),
        C.coord T (v ≫ χ) = F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap T) (C.coord T v)) ∧
      ∀ x : pt k ⟶ V.X, C.rat (x ≫ χ) = F.eval (C.rat x) := by
  have hχ : ∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ V.X),
      C.coord T (v ≫ (C.coord V.X).symm (F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap V.X) (C.coord V.X (𝟙 V.X)))) =
        F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap T) (C.coord T v) := by
    intro T v
    rw [C.coord_comp, Equiv.apply_symm_apply, appTop_eval₂_constants, ← C.coord_comp,
      Category.comp_id]
  refine ⟨_, hχ, fun x => ?_⟩
  rw [rat, hχ, ΓSpecIso_eval₂_constants_pt]
  rfl

end AddCoordinate

namespace MulCoordinate

variable (C : MulCoordinate V)

theorem val_rat_comp {X : Over (Spec (CommRingCat.of k))} (g : X ⟶ V.X) (s : pt k ⟶ X) :
    (C.rat (s ≫ g) : k) = ratHom s (C.coord X g : Γ(X.left, ⊤)) := by
  rw [val_rat, C.coord_comp]
  rfl

theorem pointHom_coord {X : Over (Spec (CommRingCat.of k))} (g : X ⟶ V.X) {B : Type u}
    [CommRing B] [Algebra k B] (t : PseudoComplete.algebraSpec k B ⟶ X) :
    pointHom t (C.coord X g : Γ(X.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom (C.coord _ (t ≫ g)).val := by
  rw [C.coord_comp]
  rfl

theorem pointHom_mul (ψ : K ⟶ V) {B : Type u} [CommRing B] [Algebra k B]
    (t₁ t₂ : PseudoComplete.algebraSpec k B ⟶ K.X) :
    pointHom (t₁ * t₂) (C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤)) =
      pointHom t₁ (C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤)) *
        pointHom t₂ (C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤)) := by
  rw [C.pointHom_coord, C.pointHom_coord, C.pointHom_coord, MonObj.mul_comp, map_mul,
    Units.val_mul]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom _ _

/-- The coordinate of a homomorphism to `V` is group-like for the comultiplication. -/
theorem exists_comul (ψ : K ⟶ V) [IsAffine K.X.left] [Algebra k Γ(K.X.left, ⊤)]
    (hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c) :
    ∃ δ : Γ(K.X.left, ⊤) →ₐ[k] Γ(K.X.left, ⊤) ⊗[k] Γ(K.X.left, ⊤),
      δ (C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤)) =
        ((C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤)) ⊗ₜ[k] 1) *
          (1 ⊗ₜ[k] (C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤))) := by
  obtain ⟨t₁, t₂, δ, h₁, h₂, hδ⟩ := StabilizerImageDichotomy.exists_comul K hA
  exact ⟨δ, by rw [hδ, C.pointHom_mul ψ, h₁, h₂]⟩

/-- The coordinates of the rational points of `V` in the image of `ψ`. -/
def image (ψ : K ⟶ V) : Subgroup kˣ where
  carrier := {c | ∃ s : pt k ⟶ K.X, C.rat (s ≫ ψ.hom.hom) = c}
  one_mem' := ⟨1, by rw [MonObj.one_comp, C.rat_one]⟩
  mul_mem' := by
    rintro _ _ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩
    exact ⟨s₁ * s₂, by rw [MonObj.mul_comp, C.rat_mul]⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨s⁻¹, by rw [GrpObj.inv_comp, C.rat_inv]⟩

theorem mem_image (ψ : K ⟶ V) {c : kˣ} :
    c ∈ C.image ψ ↔ ∃ s : pt k ⟶ K.X, C.rat (s ≫ ψ.hom.hom) = c := Iff.rfl

/-- The rational image of `ψ` consists of the values of its coordinate at the `k`-points. -/
theorem mem_image_iff (ψ : K ⟶ V) [IsAffine K.X.left] [Algebra k Γ(K.X.left, ⊤)]
    (hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c) (c : kˣ) :
    c ∈ C.image ψ ↔ (c : k) ∈ values (k := k) (C.coord K.X ψ.hom.hom : Γ(K.X.left, ⊤)) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨ratAlgHom hA s, (C.val_rat_comp _ s).symm⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨rationalPoint K.X φ.toRingHom fun c => ?_, Units.ext ?_⟩
    · rw [← hA]
      exact φ.commutes c
    · rw [C.val_rat_comp, ratHom_rationalPoint]
      exact hφ

end MulCoordinate

end Coordinates

/-! ### The two cases -/

section Cases

variable {k : Type u} [Field k] [IsAlgClosed k] {K V : GroupScheme (Spec (CommRingCat.of k))}

/-- The conclusion of `StabilizerImageDichotomyStatement` for a fixed homomorphism. -/
def Dichotomy (ψ : K ⟶ V) : Prop :=
  (∀ v : pt k ⟶ V.X, ∃ s : pt k ⟶ K.X, s ≫ ψ.hom.hom = v) ∨
    ∃ (W : Over (Spec (CommRingCat.of k))) (χ : V.X ⟶ W), IsAffine W.left ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) (s : T ⟶ K.X),
        (v * (s ≫ ψ.hom.hom)) ≫ χ = v ≫ χ) ∧
      ∀ v w : pt k ⟶ V.X, v ≫ χ = w ≫ χ → ∃ s : pt k ⟶ K.X, v * (s ≫ ψ.hom.hom) = w

/-- The dichotomy for a target with an additive coordinate (the case `𝔾ₐ`). -/
theorem dichotomy_add (ψ : K ⟶ V) [IsAffineHom K.X.hom] [LocallyOfFiniteType K.X.hom]
    [IsAffine V.X.left] (E : AddCoordinate V) : Dichotomy ψ := by
  have : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
  let : Algebra k Γ(K.X.left, ⊤) := (RelativeRoot.AdditiveGroupQuotient.structureMap K.X).toAlgebra
  have hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c := fun _ => rfl
  have : Algebra.FiniteType k Γ(K.X.left, ⊤) :=
    RingHom.finiteType_algebraMap.1 (finiteType_constants K.X)
  have hΛ := E.coe_image ψ hA
  obtain ⟨δ, hδ⟩ := E.exists_comul ψ hA
  obtain ⟨u, hu⟩ : ∃ u : Γ(K.X.left, ⊤), E.coord K.X ψ.hom.hom = u := ⟨_, rfl⟩
  rw [hu] at hΛ hδ
  have hcomp : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ K.X),
      E.coord T (s ≫ ψ.hom.hom) = s.left.appTop u := fun s => by rw [E.coord_comp, hu]
  by_cases hfin : (E.image ψ : Set k).Finite
  swap
  · left
    have hcof : (E.image ψ : Set k)ᶜ.Finite := by
      rcases values_finite_or_cofinite (k := k) u with h | h
      · exact absurd (by rw [hΛ]; exact h) hfin
      · rwa [hΛ]
    intro v
    obtain ⟨s, hs⟩ := (E.mem_image ψ).1 (add_mem_of_compl_finite (E.image ψ) hfin hcof (E.rat v))
    exact ⟨s, E.rat_injective hs⟩
  right
  have : Fintype (E.image ψ) := hfin.fintype
  obtain ⟨P, hP⟩ : ∃ P : Polynomial k, P = ∏ l : E.image ψ, (X - C (l : k)) := ⟨_, rfl⟩
  have hroot : ∀ c : k, P.eval c = 0 ↔ c ∈ E.image ψ := by
    intro c
    rw [hP, eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, eval_sub, eval_X, eval_C, sub_eq_zero]
    constructor
    · rintro ⟨l, rfl⟩
      exact l.2
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
  have hPadd : ∀ a b : k, P.eval (a + b) = P.eval a + P.eval b := by
    rw [hP]
    exact eval_add_prod_sub (E.image ψ)
  have hnil : IsNilpotent (aeval u P) := by
    apply isNilpotent_of_forall_algHom (k := k)
    intro φ
    rw [← Polynomial.aeval_algHom_apply φ u P, Polynomial.coe_aeval_eq_eval]
    refine (hroot _).2 ?_
    rw [← SetLike.mem_coe, hΛ]
    exact ⟨φ, rfl⟩
  have h0 : CharZero k → aeval u P = 0 := fun _ => aeval_eq_zero_of_primitive δ hδ P hPadd hnil
  obtain ⟨e, he⟩ := exists_pow_expChar_pow_eq_zero (ringExpChar k) hnil h0
  obtain ⟨F, hF⟩ : ∃ F : Polynomial k, F = P ^ ringExpChar k ^ e := ⟨_, rfl⟩
  have hFadd : ∀ a b : k, F.eval (a + b) = F.eval a + F.eval b := by
    intro a b
    simp only [hF, eval_pow, hPadd, add_pow_expChar_pow]
  have hFu : F.eval₂ (RelativeRoot.AdditiveGroupQuotient.structureMap K.X) u = 0 := by
    change aeval u F = 0
    rw [hF, map_pow, he]
  have hFroot : ∀ c : k, F.eval c = 0 → c ∈ E.image ψ := by
    intro c hc
    rw [hF, eval_pow] at hc
    exact (hroot c).1 ((pow_eq_zero_iff (pow_ne_zero _ (expChar_pos k (ringExpChar k)).ne')).1 hc)
  obtain ⟨χ, hχ, hval⟩ := E.exists_polynomial_map F
  refine ⟨V.X, χ, inferInstance, fun T v s => ?_, fun v w hvw => ?_⟩
  · apply (E.coord T).injective
    rw [hχ, hχ, E.coord_mul, hcomp, eval₂_add_of_eval_add F hFadd, ← appTop_eval₂_constants,
      hFu, map_zero, add_zero]
  · have h1 := congrArg E.rat hvw
    rw [hval, hval] at h1
    have hmem : E.rat w - E.rat v ∈ E.image ψ := by
      apply hFroot
      have h2 := hFadd (E.rat w - E.rat v) (E.rat v)
      rw [sub_add_cancel, ← h1] at h2
      linear_combination -h2
    obtain ⟨s, hs⟩ := (E.mem_image ψ).1 hmem
    refine ⟨s, E.rat_injective ?_⟩
    rw [E.rat_mul, hs]
    ring

/-- The dichotomy for a target with a multiplicative coordinate (the case `𝔾ₘ`). -/
theorem dichotomy_mul (ψ : K ⟶ V) [IsAffineHom K.X.hom] [LocallyOfFiniteType K.X.hom]
    [IsAffine V.X.left] (E : MulCoordinate V) : Dichotomy ψ := by
  have : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
  let : Algebra k Γ(K.X.left, ⊤) := (RelativeRoot.AdditiveGroupQuotient.structureMap K.X).toAlgebra
  have hA : ∀ c, algebraMap k Γ(K.X.left, ⊤) c = RelativeRoot.AdditiveGroupQuotient.structureMap K.X c := fun _ => rfl
  have : Algebra.FiniteType k Γ(K.X.left, ⊤) :=
    RingHom.finiteType_algebraMap.1 (finiteType_constants K.X)
  have hΛ := E.mem_image_iff ψ hA
  obtain ⟨δ, hδ⟩ := E.exists_comul ψ hA
  obtain ⟨u, hu⟩ : ∃ u : (Γ(K.X.left, ⊤))ˣ, E.coord K.X ψ.hom.hom = u := ⟨_, rfl⟩
  rw [hu] at hΛ hδ
  have hcomp : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ K.X),
      (E.coord T (s ≫ ψ.hom.hom) : Γ(T.left, ⊤)) = s.left.appTop (u : Γ(K.X.left, ⊤)) :=
    fun s => by
      rw [E.coord_comp, hu]
      rfl
  by_cases hfin : (E.image ψ : Set kˣ).Finite
  swap
  · left
    have hcof : (E.image ψ : Set kˣ)ᶜ.Finite := by
      rcases values_finite_or_cofinite (k := k) (u : Γ(K.X.left, ⊤)) with h | h
      · exact absurd ((h.preimage Units.val_injective.injOn).subset fun c hc => (hΛ c).1 hc)
          hfin
      · exact (h.preimage Units.val_injective.injOn).subset fun c hc hc' => hc ((hΛ c).2 hc')
    intro v
    obtain ⟨s, hs⟩ := (E.mem_image ψ).1 (mem_of_compl_finite (E.image ψ) hfin hcof (E.rat v))
    exact ⟨s, E.rat_injective hs⟩
  right
  have : Finite (E.image ψ) := hfin.to_subtype
  have hpow : ∀ c ∈ E.image ψ, c ^ Nat.card (E.image ψ) = 1 := fun c hc =>
    congrArg Subtype.val (pow_card_eq_one' (G := E.image ψ) (x := ⟨c, hc⟩))
  have hΛμ : E.image ψ = rootsOfUnity (Nat.card (E.image ψ)) k := by
    have : NeZero (Nat.card (E.image ψ)) := ⟨Nat.card_pos.ne'⟩
    apply Subgroup.eq_of_le_of_card_ge
    · intro c hc
      exact (mem_rootsOfUnity _ c).2 (hpow c hc)
    · exact card_rootsOfUnity (R := k) (k := Nat.card (E.image ψ))
  obtain ⟨m, hm⟩ : ∃ m, Nat.card (E.image ψ) = m := ⟨_, rfl⟩
  rw [hm] at hpow hΛμ
  have hnil : IsNilpotent ((u : Γ(K.X.left, ⊤)) ^ m - 1) := by
    apply isNilpotent_of_forall_algHom (k := k)
    intro φ
    have hc : Units.map (φ : Γ(K.X.left, ⊤) →* k) u ∈ E.image ψ := (hΛ _).2 ⟨φ, rfl⟩
    have h1 : (Units.map (φ : Γ(K.X.left, ⊤) →* k) u : k) = φ u := rfl
    rw [map_sub, map_pow, map_one, ← h1, ← Units.val_pow_eq_pow_val, hpow _ hc, Units.val_one,
      sub_self]
  have h0 : CharZero k → (u : Γ(K.X.left, ⊤)) ^ m - 1 = 0 := fun _ =>
    pow_sub_one_eq_zero_of_grouplike δ u.isUnit hδ m hnil
  obtain ⟨e, he⟩ := exists_pow_expChar_pow_eq_zero (ringExpChar k) hnil h0
  have : Nontrivial Γ(K.X.left, ⊤) := (ratHom (1 : pt k ⟶ K.X)).domain_nontrivial
  have : ExpChar Γ(K.X.left, ⊤) (ringExpChar k) :=
    expChar_of_injective_algebraMap (algebraMap k Γ(K.X.left, ⊤)).injective _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = m * ringExpChar k ^ e := ⟨_, rfl⟩
  have huN : (u : Γ(K.X.left, ⊤)) ^ N = 1 := by
    have h := sub_pow_expChar_pow ((u : Γ(K.X.left, ⊤)) ^ m) 1 e (p := ringExpChar k)
    rw [one_pow, he] at h
    rw [hN, pow_mul]
    exact (sub_eq_zero.1 h.symm)
  have hχ : ∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ V.X), v ≫ (𝟙 V.X) ^ N = v ^ N :=
    fun v => by rw [MonObj.comp_pow, Category.comp_id]
  refine ⟨V.X, (𝟙 V.X) ^ N, inferInstance, fun T v s => ?_, fun v w hvw => ?_⟩
  · rw [hχ, hχ]
    apply (E.coord T).injective
    have h1 : E.coord T (s ≫ ψ.hom.hom) ^ N = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hcomp, ← map_pow, huN, map_one, Units.val_one]
    rw [map_pow, map_mul, map_pow, mul_pow, h1, _root_.mul_one]
  · have h1 := congrArg E.rat hvw
    rw [hχ, hχ, E.rat_pow, E.rat_pow] at h1
    have hcN : ((E.rat v)⁻¹ * E.rat w) ^ N = 1 := by
      rw [mul_pow, inv_pow, h1, inv_mul_cancel]
    have hc : ((E.rat v)⁻¹ * E.rat w) ^ m = 1 := by
      apply Units.ext
      apply eq_one_of_pow_expChar_pow_eq_one (ringExpChar k) e
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← hN, hcN, Units.val_one]
    have hmem : (E.rat v)⁻¹ * E.rat w ∈ E.image ψ := by
      rw [hΛμ]
      exact (mem_rootsOfUnity _ _).2 hc
    obtain ⟨s, hs⟩ := (E.mem_image ψ).1 hmem
    refine ⟨s, E.rat_injective ?_⟩
    rw [E.rat_mul, hs, mul_inv_cancel_left]

end Cases

end StabilizerImageDichotomy

open StabilizerImageDichotomy in
theorem stabilizerImageDichotomy : StabilizerImageDichotomyStatement.{u} := by
  intro k _ _ K V _ _ ψ hV
  rcases hV with hV | hV
  · have : IsAffineHom V.X.hom := hV.isAffineHom
    have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
    exact dichotomy_add ψ (AddCoordinate.ofVectorGroup hV)
  · obtain ⟨f⟩ := hV
    have : IsIso f.hom.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).map f.hom))
    have : IsAffine (Gm (Spec (CommRingCat.of k))).X.left := by
      change IsAffine (CategoryTheory.Limits.pullback
        (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
        (Gm.toSpecZ (Spec (CommRingCat.of k))))
      infer_instance
    have : IsAffine V.X.left := IsAffine.of_isIso f.hom.hom.hom.left
    exact dichotomy_mul ψ (MulCoordinate.ofIso f)

end Langlands.GroupScheme
