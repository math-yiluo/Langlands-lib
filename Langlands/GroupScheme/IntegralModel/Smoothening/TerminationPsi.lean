import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationKrull
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Graded independence from formal smoothness

Let `E` be a formally smooth algebra over an infinite field `k` with a `k`-point `e`, and let
`x j` be elements of the augmentation ideal whose differentials are linearly independent. Then a
homogeneous polynomial of degree `n` in the `x j` that lies in the `(n+1)`-st power of the
augmentation ideal has all its coefficients in the augmentation ideal. The proof maps `E` to the
truncated polynomial rings `k[T]/(T^(n+1))`, sending `x j` to `a j T + O(T²)`, by lifting a first
order map along the nilpotent surjection `k[T]/(T^(n+1)) → k[T]/(T²)`. -/

noncomputable section

open Polynomial

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {k : Type*} [Field k]

/-- The truncated polynomial ring `k[T]/(T^(m))`. -/
abbrev Trunc (k : Type*) [Field k] (m : ℕ) := k[X] ⧸ Ideal.span {(X : k[X]) ^ m}

theorem coeff_eq_zero_of_mem_span {m n : ℕ} (hnm : n < m) {p : k[X]}
    (hp : p ∈ Ideal.span {(X : k[X]) ^ m}) : p.coeff n = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  rw [mul_comm, coeff_X_pow_mul', ite_eq_right_iff]
  intro h
  omega

variable {E : Type*} [CommRing E] [Algebra k E] (e : E →ₐ[k] k)

/-- The first order map `E → k[T]/(T²)`, `y ↦ e y + λ(dy) T`. -/
def firstOrder (l : Cot e →ₗ[k] k) : E →ₐ[k] Trunc k 2 where
  toFun y := Ideal.Quotient.mk _ (C (e y) + C (l (dif e y)) * X)
  map_one' := by
    rw [map_one, dif_one, map_zero, C_0, zero_mul, add_zero, C_1, map_one]
  map_mul' y y' := by
    rw [← map_mul, Ideal.Quotient.eq]
    have : C (e (y * y')) + C (l (dif e (y * y'))) * X -
        (C (e y) + C (l (dif e y)) * X) * (C (e y') + C (l (dif e y')) * X) =
        -(C (l (dif e y) * l (dif e y')) * X ^ 2) := by
      rw [dif_mul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [C_mul, C_add]
      ring
    rw [this]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  map_zero' := by
    simp
  map_add' y y' := by
    rw [← map_add]
    congr 1
    simp only [map_add]
    ring
  commutes' r := by
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, dif_algebraMap, map_zero,
      C_0, zero_mul, add_zero]
    rfl

theorem firstOrder_apply (l : Cot e →ₗ[k] k) (y : E) :
    firstOrder e l y = Ideal.Quotient.mk _ (C (e y) + C (l (dif e y)) * X) := rfl

theorem span_pow_le_span_sq (n : ℕ) :
    Ideal.span {(X : k[X]) ^ (n + 2)} ≤ Ideal.span {(X : k[X]) ^ 2} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow X (by omega))

/-- The truncation map `k[T]/(T^(n+2)) → k[T]/(T²)`. -/
def truncMap (n : ℕ) : Trunc k (n + 2) →ₐ[k] Trunc k 2 :=
  Ideal.Quotient.factorₐ k (span_pow_le_span_sq n)

theorem truncMap_mk (n : ℕ) (p : k[X]) :
    truncMap (k := k) n (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

theorem truncMap_surjective (n : ℕ) : Function.Surjective (truncMap (k := k) n) :=
  Ideal.Quotient.factor_surjective (span_pow_le_span_sq n)

theorem truncMap_ker_nilpotent (n : ℕ) :
    IsNilpotent (RingHom.ker (truncMap (k := k) n : Trunc k (n + 2) →+* Trunc k 2)) := by
  refine ⟨n + 2, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  have hker : RingHom.ker (truncMap (k := k) n : Trunc k (n + 2) →+* Trunc k 2) ≤
      Ideal.span {Ideal.Quotient.mk _ ((X : k[X]) ^ 2)} := by
    intro b hb
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    have : Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ 2}) p = 0 := hb
    rw [Ideal.Quotient.eq_zero_iff_mem] at this
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp this
    rw [map_mul, mul_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine (Ideal.pow_right_mono hker _).trans ?_
  rw [Ideal.span_singleton_pow, ← map_pow, ← pow_mul]
  intro b hb
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem.mpr, mul_zero]
  exact Ideal.mem_span_singleton.mpr (pow_dvd_pow X (by omega))

theorem exists_functional {V : Type*} [AddCommGroup V] [Module k V] {t : ℕ} {v : Fin t → V}
    (hv : LinearIndependent k v) (a : Fin t → k) : ∃ l : V →ₗ[k] k, ∀ j, l (v j) = a j := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr k a)
  refine ⟨g, fun j => ?_⟩
  have := congrArg (fun f : _ →ₗ[k] k => f (Module.Basis.span hv j)) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    Module.Basis.constr_basis] at this
  rw [Module.Basis.span_apply] at this
  exact this

section Main

variable [Algebra.FormallySmooth k E]

/-- A lift of the first order map to `k[T]/(T^(n+2))`. -/
def psiMap (l : Cot e →ₗ[k] k) (n : ℕ) : E →ₐ[k] Trunc k (n + 2) :=
  Algebra.FormallySmooth.liftOfSurjective (firstOrder e l) (truncMap n) (truncMap_surjective n)
    (truncMap_ker_nilpotent n)

theorem psiMap_spec (l : Cot e →ₗ[k] k) (n : ℕ) (y : E) :
    truncMap n (psiMap e l n y) = firstOrder e l y :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y

/-- A representative of `psiMap y` is congruent to `e y + l(dy) T` modulo `T²`. -/
theorem psiMap_rep (l : Cot e →ₗ[k] k) (n : ℕ) (y : E) :
    ∃ s : k[X], psiMap e l n y = Ideal.Quotient.mk _ (C (e y) + C (l (dif e y)) * X + X ^ 2 * s) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (psiMap e l n y)
  have h := psiMap_spec e l n y
  rw [← hp, truncMap_mk, firstOrder_apply, Ideal.Quotient.eq] at h
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨s, ?_⟩
  rw [← hp]
  congr 1
  linear_combination -hs

/-- **Graded independence from formal smoothness.** -/
theorem coeff_eq_zero_of_formallySmooth [Infinite k] {t : ℕ} (x : Fin t → E)
    (hx : ∀ j, x j ∈ augIdeal e) (hind : LinearIndependent k (fun j => dif e (x j))) (n : ℕ)
    (P : MvPolynomial (Fin t) E) (hP : P.IsHomogeneous n)
    (hPx : MvPolynomial.eval x P ∈ augIdeal e ^ (n + 1)) (μ : Fin t →₀ ℕ) :
    e (P.coeff μ) = 0 := by
  suffices h : MvPolynomial.map (e : E →+* k) P = 0 by
    have := MvPolynomial.ext_iff.mp h μ
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at this
    exact this
  apply MvPolynomial.funext
  intro a
  rw [map_zero]
  obtain ⟨l, hl⟩ := exists_functional hind a
  set ψ := psiMap e l n
  classical
  -- representatives of the images of the variables and of the coefficients
  choose s hs using fun y => psiMap_rep e l n y
  have hxe : ∀ j, e (x j) = 0 := fun j => hx j
  -- `ψ` maps the augmentation ideal into `(T)`
  have hψI : Ideal.map ψ (augIdeal e) ≤ Ideal.span {Ideal.Quotient.mk _ (X : k[X])} := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, hs y, RingHom.mem_ker.mp hy, C_0, zero_add]
    refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (C (l (dif e y)) + X * s y), ?_⟩
    rw [← map_mul]
    congr 1
    ring
  have hzero : ψ (MvPolynomial.eval x P) ∈ Ideal.span {Ideal.Quotient.mk
      (Ideal.span {(X : k[X]) ^ (n + 2)}) ((X : k[X]) ^ (n + 1))} := by
    have h1 : ψ (MvPolynomial.eval x P) ∈ Ideal.map ψ (augIdeal e ^ (n + 1)) :=
      Ideal.mem_map_of_mem _ hPx
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hψI (n + 1) h1
    rwa [Ideal.span_singleton_pow, ← map_pow] at h2
  -- compute the image through representatives
  set F : k[X] := ∑ ν ∈ P.support, (C (e (P.coeff ν)) + C (l (dif e (P.coeff ν))) * X +
      X ^ 2 * s (P.coeff ν)) * ∏ j, (C (a j) * X + X ^ 2 * s (x j)) ^ ν j with hF
  have hψF : ψ (MvPolynomial.eval x P) = Ideal.Quotient.mk _ F := by
    rw [MvPolynomial.eval_eq', map_sum, hF, map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_mul, map_prod, map_mul, map_prod, hs]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, map_pow, hs, hxe, hl, C_0, zero_add]
  -- `F` lies in `(T^(n+1))`, so its `n`-th coefficient vanishes
  have hFmem : F ∈ Ideal.span {(X : k[X]) ^ (n + 1)} := by
    rw [hψF] at hzero
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hzero
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq] at hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
    refine Ideal.mem_span_singleton'.mpr ⟨q - r * X, ?_⟩
    linear_combination -hr
  have hcoeff := coeff_eq_zero_of_mem_span (Nat.lt_succ_self n) hFmem
  -- the `n`-th coefficient of `F` is the value of the reduced polynomial at `a`
  have hFX : F = X ^ n * ∑ ν ∈ P.support, (C (e (P.coeff ν)) + C (l (dif e (P.coeff ν))) * X +
      X ^ 2 * s (P.coeff ν)) * ∏ j, (C (a j) + X * s (x j)) ^ ν j := by
    rw [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν hν => ?_
    have hdeg : ∑ j, ν j = n := by
      have := hP (MvPolynomial.mem_support_iff.mp hν)
      have h2 : ν.degree = n := by rw [Finsupp.degree_eq_weight_one]; exact this
      rwa [Finsupp.degree_eq_sum] at h2
    have : ∏ j, (C (a j) * X + X ^ 2 * s (x j)) ^ ν j =
        X ^ n * ∏ j, (C (a j) + X * s (x j)) ^ ν j := by
      rw [← hdeg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_pow]
      congr 1
      ring
    rw [this]
    ring
  rw [hFX, coeff_X_pow_mul'] at hcoeff
  simp only [le_refl, ↓reduceIte, Nat.sub_self] at hcoeff
  rw [coeff_zero_eq_eval_zero, eval_finsetSum] at hcoeff
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq', ← hcoeff]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp [eval_prod]

end Main

section Bridge

variable {R : Type*} [CommRing R] [IsLocalRing R] {C : Type*} [CommRing C] [Algebra R C]
  {E : Type*} [CommRing E] [Algebra R E] [Algebra (IsLocalRing.ResidueField R) E]
  [IsScalarTower R (IsLocalRing.ResidueField R) E]

/-- **Graded independence for `C` from formal smoothness of `C ⧸ J`.** Here `E` plays the role of
`C ⧸ J` as an algebra over the residue field, `π : C → E` is the quotient map and `e` is the point
of `E` induced by `ε`. -/
theorem gradedIndep_of_formallySmooth [Infinite (IsLocalRing.ResidueField R)]
    [Algebra.FormallySmooth (IsLocalRing.ResidueField R) E]
    (ε : C →ₐ[R] R) {ϖ : R} (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (J : Ideal C)
    (π : C →ₐ[R] E) (hπ : Function.Surjective π) (hker : RingHom.ker π = J)
    (e : E →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R)
    (he : ∀ y, e (π y) = IsLocalRing.residue R (ε y))
    {t : ℕ} (x : Fin t → C) (hx : ∀ j, x j ∈ augIdeal ε)
    (hxind : ∀ a : Fin t → R, (∑ j, a j • x j) ∈ J ⊔ augIdeal ε ^ 2 →
      ∀ j, a j ∈ IsLocalRing.maximalIdeal R) :
    GradedIndep ε ϖ x J := by
  set k := IsLocalRing.ResidueField R
  have hπx : ∀ j, π (x j) ∈ augIdeal e := fun j => by
    rw [RingHom.mem_ker, he, RingHom.mem_ker.mp (hx j), map_zero]
  -- the augmentation ideal of `E` pulls back into `J ⊔ I ^ 2` after squaring
  have hpull : ∀ y : C, π y ∈ augIdeal e ^ 2 → y ∈ J ⊔ augIdeal ε ^ 2 := by
    intro y hy
    have hmap : augIdeal e = Ideal.map π (augIdeal ε) := by
      apply le_antisymm
      · intro w hw
        obtain ⟨y, rfl⟩ := hπ w
        have hy' : ε y ∈ IsLocalRing.maximalIdeal R := by
          rw [← IsLocalRing.residue_eq_zero_iff, ← he]
          exact hw
        have h0 : algebraMap R E (ε y) = 0 := by
          rw [IsScalarTower.algebraMap_apply R k E, IsLocalRing.ResidueField.algebraMap_eq,
            (IsLocalRing.residue_eq_zero_iff _).mpr hy', map_zero]
        have hsplit : π y = π (y - algebraMap R C (ε y)) := by
          rw [map_sub, AlgHom.commutes, h0, sub_zero]
        rw [hsplit]
        exact Ideal.mem_map_of_mem _ (sub_algebraMap_mem ε y)
      · rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [Ideal.mem_comap, RingHom.mem_ker, he, RingHom.mem_ker.mp hy, map_zero]
    rw [hmap, ← Ideal.map_pow] at hy
    obtain ⟨y', hy', hyy'⟩ := (Ideal.mem_map_iff_of_surjective _ hπ).mp hy
    have : y - y' ∈ J := by
      rw [← hker, RingHom.mem_ker, map_sub, hyy', sub_self]
    have hyeq : y = (y - y') + y' := by ring
    rw [hyeq]
    exact Submodule.add_mem_sup this hy'
  -- linear independence of the differentials of the `π (x j)`
  have hind : LinearIndependent k (fun j => dif e (π (x j))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    choose a ha using fun i => IsLocalRing.residue_surjective (c i)
    have hsum : π (∑ i, a i • x i) = ∑ i, c i • π (x i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← ha i, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
    have hmemI : π (∑ i, a i • x i) ∈ augIdeal e := by
      rw [map_sum]
      exact Ideal.sum_mem _ fun i _ => by
        rw [map_smul]
        exact Submodule.smul_of_tower_mem _ _ (hπx i)
    have hd0 : dif e (π (∑ i, a i • x i)) = 0 := by
      rw [hsum, map_sum]
      simp_rw [map_smul]
      exact hc
    rw [dif_of_mem e hmemI, Ideal.toCotangent_eq_zero] at hd0
    have := hxind a (hpull _ hd0) j
    rw [← ha j]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr this
  intro n P hP hPJ μ
  have hmI : Ideal.map π (ptIdeal ε ϖ) ≤ augIdeal e := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [ptIdeal, Ideal.mem_comap, ← hϖ] at hy
    rw [Ideal.mem_comap, RingHom.mem_ker, he, (IsLocalRing.residue_eq_zero_iff _).mpr hy]
  have hev : MvPolynomial.eval (fun j => π (x j)) (MvPolynomial.map (π : C →+* E) P) ∈
      augIdeal e ^ (n + 1) := by
    have hme : MvPolynomial.eval (fun j => π (x j)) (MvPolynomial.map (π : C →+* E) P) =
        (π : C →+* E) (MvPolynomial.eval x P) := (MvPolynomial.map_eval (π : C →+* E) x P).symm
    rw [hme]
    obtain ⟨j0, hj0, w, hw, hjw⟩ := Submodule.mem_sup.mp hPJ
    have hπj : π j0 = 0 := by
      rw [← RingHom.mem_ker]
      change j0 ∈ RingHom.ker (π : C →+* E)
      rw [show RingHom.ker (π : C →+* E) = J from hker]
      exact hj0
    change π (MvPolynomial.eval x P) ∈ _
    rw [← hjw, map_add, hπj, zero_add]
    have := Ideal.mem_map_of_mem π hw
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmI _ this
  have h := coeff_eq_zero_of_formallySmooth e (fun j => π (x j)) hπx hind n _
    (hP.map _) hev μ
  rw [MvPolynomial.coeff_map] at h
  change e (π (P.coeff μ)) = 0 at h
  rw [he, IsLocalRing.residue_eq_zero_iff, hϖ] at h
  rw [ptIdeal, Ideal.mem_comap]
  exact h

end Bridge

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
