import Langlands.Algebra.CentralSimple.NumberFieldUnitaryLocalRootNeighborhoodStatement
import Langlands.Global.AdelicSpaceLocalFields
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower

/-!
# Unitary roots of nearby conjugate-reciprocal polynomials: proof

This file proves `Langlands.CentralSimple.NumberFieldUnitaryLocalRootNeighborhoodStatement`, the
unitary form of Krasner's lemma used in the proof of Theorem 6.28 of Platonov and Rapinchuk,
*Algebraic Groups and Number Theory*. The proof applies the inverse function theorem to
polynomial evaluation with varying coefficients.

Write `K = F_v`, `A = K ⊗[F] E` and `ψ : A → K ⊗[F] B`. The image of `ψ` is central, so
`p ↦ p.eval₂ ψ x` factors through the commutative ring `S = A[X]/(f)` (`AdjoinRoot f`); the
resulting ring map `φ : S → K ⊗[F] B` is injective because `1, x, …, x^{n-1}` are independent
over `A` and `S` is free over `A` with basis `1, X, …, X^{n-1}`. The class `X` of the variable is
a unit of `S` because the constant coefficient `(-1)ⁿ (1 ⊗ z)` of `f` is a unit, and the
conjugate-reciprocal relation makes `X⁻¹` a root of the conjugate polynomial, so there is a
ring endomorphism `σ` of `S` acting on `A` by `c_v` with `σ X = X⁻¹`; it satisfies
`τ_v ∘ φ = φ ∘ σ`.

The commutative `K`-algebra `S` is finite-dimensional; it is normed through its left regular
representation in matrices with the `L^∞`-operator norm. With `G(y, p) = yⁿ + ∑ L_i(p) yⁱ`, where
`L_i(p) ∈ S` is the coefficient with coordinates `p i`, the map `(y, p) ↦ (G(y, p), p)` has an
invertible strict derivative at `(X, coordinates of f)`, since `f'(X)` is a unit of `S`; the
inverse function theorem gives a neighbourhood of `X` in which every `g` with nearby coordinates
has exactly one root (`exists_root_nhds`). For conjugate-reciprocal `g` and a root `y`,
`σ(y)⁻¹` is again a root (`aeval_inv_eq_zero_of_reflect`) and is close to `σ(X)⁻¹ = X`, so
uniqueness gives `y σ(y) = 1`; linear independence of `1, y, …, y^{n-1}` is an open condition
(`exists_unitary_root_nhds`). Applying `φ` transports the root to `K ⊗[F] B`
(`local_root_neighborhood`). The completion at an archimedean or finite place is a complete
nontrivially normed field inducing its topology (`Langlands.Global.AdelicSpaceLocalFields`).
-/

noncomputable section

open scoped TensorProduct
open Polynomial Filter Topology

namespace Langlands.CentralSimple.UnitaryKrasner

open Langlands.GroupScheme.Quaternionic

section RootNeighborhood

variable {K S P : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedCommRing S] [NormedAlgebra K S] [FiniteDimensional K S]
  [NormedAddCommGroup P] [NormedSpace K P] [FiniteDimensional K P]

/-- **Roots of nearby polynomials in a finite-dimensional commutative normed algebra.** Let
`G(y, p) = yⁿ + ∑ᵢ Lᵢ(p) yⁱ` with continuous linear coefficient maps `Lᵢ : P → S`. If `y₀` is a
root of `G(·, p₀)` at which the derivative `n y₀^{n-1} + ∑ᵢ Lᵢ(p₀) i y₀^{i-1}` is a unit, then
there are neighbourhoods `N₀` of `y₀` and `V₀` of `p₀` such that `G(·, p)` has at most one root
in `N₀` for `p ∈ V₀`, and for every neighbourhood `N` of `y₀`, `G(·, p)` has a root in `N` for
all `p` near `p₀`. This is the inverse function theorem for `(y, p) ↦ (G(y, p), p)`. -/
theorem exists_root_nhds {n : ℕ} (L : Fin n → P →L[K] S) (y₀ : S) (p₀ : P)
    (h₀ : y₀ ^ n + ∑ i : Fin n, L i p₀ * y₀ ^ (i : ℕ) = 0)
    (hu : IsUnit ((n : S) * y₀ ^ (n - 1) +
      ∑ i : Fin n, L i p₀ * ((i : ℕ) * y₀ ^ ((i : ℕ) - 1)))) :
    ∃ N₀ ∈ 𝓝 y₀, ∃ V₀ ∈ 𝓝 p₀, (∀ p ∈ V₀, ∀ y ∈ N₀, ∀ y' ∈ N₀,
        y ^ n + ∑ i : Fin n, L i p * y ^ (i : ℕ) = 0 →
        y' ^ n + ∑ i : Fin n, L i p * y' ^ (i : ℕ) = 0 → y = y') ∧
      ∀ N ∈ 𝓝 y₀, ∀ᶠ p in 𝓝 p₀, ∃ y ∈ N, y ^ n + ∑ i : Fin n, L i p * y ^ (i : ℕ) = 0 := by
  have : CompleteSpace S := FiniteDimensional.complete K S
  have : CompleteSpace P := FiniteDimensional.complete K P
  let G : S × P → S := fun q => q.1 ^ n + ∑ i : Fin n, L i q.2 * q.1 ^ (i : ℕ)
  let a : S × P := (y₀, p₀)
  let D : S × P →L[K] S := (n • y₀ ^ (n - 1)) • ContinuousLinearMap.fst K S P +
    ∑ i : Fin n, (L i p₀ • (((i : ℕ) • y₀ ^ ((i : ℕ) - 1)) • ContinuousLinearMap.fst K S P) +
      y₀ ^ (i : ℕ) • ((L i).comp (ContinuousLinearMap.snd K S P)))
  have hG : HasStrictFDerivAt G D a := by
    apply HasStrictFDerivAt.add
    · exact HasStrictFDerivAt.pow (𝕜 := K) (𝔸 := S) (hasStrictFDerivAt_fst (𝕜 := K) (p := a)) n
    · apply HasStrictFDerivAt.fun_sum
      intro i _
      exact ((L i).hasStrictFDerivAt.comp a hasStrictFDerivAt_snd).fun_mul
        (HasStrictFDerivAt.pow (𝕜 := K) (𝔸 := S) (hasStrictFDerivAt_fst (𝕜 := K) (p := a)) (i : ℕ))
  let Ψ : S × P → S × P := fun q => (G q, q.2)
  let D' : S × P →L[K] S × P := D.prod (ContinuousLinearMap.snd K S P)
  have hΨ : HasStrictFDerivAt Ψ D' a := hG.prodMk hasStrictFDerivAt_snd
  have hD (h : S) : D (h, 0) = ((n : S) * y₀ ^ (n - 1) +
      ∑ i : Fin n, L i p₀ * ((i : ℕ) * y₀ ^ ((i : ℕ) - 1))) * h := by
    simp [D, nsmul_eq_mul, add_mul, Finset.sum_mul, mul_assoc]
  have hinj : Function.Injective D' := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨h, k⟩ hq
    simp only [D', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
      Prod.mk_eq_zero] at hq
    obtain ⟨h1, rfl⟩ := hq
    rw [hD] at h1
    rw [Prod.mk_eq_zero]
    exact ⟨(hu.mul_right_eq_zero).mp h1, rfl⟩
  let e : (S × P) ≃ₗ[K] (S × P) := LinearEquiv.ofInjectiveEndo D'.toLinearMap hinj
  let e' : (S × P) ≃L[K] (S × P) := e.toContinuousLinearEquiv
  have he' : (e' : S × P →L[K] S × P) = D' := ContinuousLinearMap.ext fun q => rfl
  have hΨ' : HasStrictFDerivAt Ψ (e' : S × P →L[K] S × P) a := he' ▸ hΨ
  have hΨa : Ψ a = (0, p₀) := by
    simp only [Ψ, G, a, h₀]
  have hleft : {q | hΨ'.localInverse Ψ e' a (Ψ q) = q} ∈ 𝓝 y₀ ×ˢ 𝓝 p₀ := by
    rw [← nhds_prod_eq]
    exact hΨ'.eventually_left_inverse
  obtain ⟨N₀, hN₀, V₀, hV₀, hsub⟩ := Filter.mem_prod_iff.mp hleft
  refine ⟨N₀, hN₀, V₀, hV₀, ?_, ?_⟩
  · intro p hp y hy y' hy' h1 h2
    have e1 : _ = (y, p) := hsub (Set.mk_mem_prod hy hp)
    have e2 : _ = (y', p) := hsub (Set.mk_mem_prod hy' hp)
    have hΨe : Ψ (y, p) = Ψ (y', p) := by
      simp only [Ψ, G]
      rw [h1, h2]
    rw [hΨe] at e1
    exact congrArg Prod.fst (e1.symm.trans e2)
  · intro N hN
    have ht : Tendsto (fun p : P => ((0 : S), p)) (𝓝 p₀) (𝓝 (Ψ a)) := by
      rw [hΨa]
      exact (continuous_const.prodMk continuous_id).tendsto _
    have hr := ht.eventually hΨ'.eventually_right_inverse
    have hl := ht.eventually (hΨ'.localInverse_tendsto.eventually
      (prod_mem_nhds hN Filter.univ_mem))
    filter_upwards [hr, hl] with p hp1 hp2
    refine ⟨(hΨ'.localInverse Ψ e' a (0, p)).1, hp2.1, ?_⟩
    have h2 : (hΨ'.localInverse Ψ e' a (0, p)).2 = p := congrArg Prod.snd hp1
    have h1 : G (hΨ'.localInverse Ψ e' a (0, p)) = 0 := congrArg Prod.fst hp1
    simp only [G, h2] at h1
    exact h1

end RootNeighborhood

section Polynomials

open Polynomial

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- Evaluation of a monic polynomial of natural degree `n`. -/
theorem aeval_monic_eq {g : A[X]} (hg : g.Monic) {n : ℕ} (hd : g.natDegree = n) (y : R) :
    aeval y g = y ^ n + ∑ i : Fin n, algebraMap A R (g.coeff i) * y ^ (i : ℕ) := by
  conv_lhs => rw [hg.as_sum]
  subst hd
  rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap A R (g.coeff i) * y ^ i)]
  simp [map_sum]

/-- Evaluation of the derivative of a monic polynomial of natural degree `n`. -/
theorem aeval_derivative_monic_eq {g : A[X]} (hg : g.Monic) {n : ℕ} (hd : g.natDegree = n)
    (y : R) : aeval y (derivative g) = (n : R) * y ^ (n - 1) +
      ∑ i : Fin n, algebraMap A R (g.coeff i) * ((i : ℕ) * y ^ ((i : ℕ) - 1)) := by
  conv_lhs => rw [hg.as_sum]
  subst hd
  rw [Fin.sum_univ_eq_sum_range
    (fun i => algebraMap A R (g.coeff i) * ((i : R) * y ^ (i - 1)))]
  simp [map_sum, derivative_X_pow]

/-- A polynomial of degree at most `n` with `g_{n-i} = (-1)ⁿ ζ c(g_i)` for `i ≤ n` has reflection
`(-1)ⁿ ζ · c(g)`. -/
theorem reflect_eq_of_conjRecip (cA : A →+* A) (ζ : A) {n : ℕ} {g : A[X]}
    (hgd : g.natDegree ≤ n)
    (hgc : ∀ i ≤ n, g.coeff (n - i) = (-1) ^ n * ζ * cA (g.coeff i)) :
    reflect n g = C ((-1) ^ n * ζ) * g.map cA := by
  ext i
  rw [coeff_reflect, coeff_C_mul, coeff_map]
  by_cases hi : i ≤ n
  · rw [revAt_le hi, hgc i hi]
  · rw [not_le] at hi
    rw [revAt_eq_self_of_lt hi, coeff_eq_zero_of_natDegree_lt (hgd.trans_lt hi), map_zero,
      mul_zero]

/-- If the reflection of `q` (in degree `N ≥ deg q`) is a multiple of `r` and the unit `w` is a
root of `r`, then `w⁻¹` is a root of `q`. -/
theorem aeval_inv_eq_zero_of_reflect (w : Rˣ) {q r : A[X]} {c : A} {N : ℕ}
    (hq : q.natDegree ≤ N) (h : reflect N q = C c * r) (hr : aeval (w : R) r = 0) :
    aeval ((w⁻¹ : Rˣ) : R) q = 0 := by
  let : Invertible ((w⁻¹ : Rˣ) : R) := Units.invertible (w⁻¹)
  have key := eval₂_reflect_mul_pow (algebraMap A R) ((w⁻¹ : Rˣ) : R) N q hq
  have hinv : ⅟((w⁻¹ : Rˣ) : R) = (w : R) := by
    simp
  rw [aeval_def, ← key, hinv, h, eval₂_mul, eval₂_C, ← aeval_def, hr, mul_zero, zero_mul]

end Polynomials

section UnitaryRoot

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]
  {S : Type*} [CommRing S] [Algebra A S] [Algebra K S] [IsScalarTower K A S]
  [FiniteDimensional K S]
  {ι : Type*} [Fintype ι]

/-- **Unitary roots in a finite-dimensional commutative algebra.** Let `S` be a commutative
algebra over `A`, finite-dimensional over the complete field `K`, with a `K`-algebra endomorphism
`σ` acting on `A` by `cA`. Let `y₀ ∈ S` with `y₀ σ(y₀) = 1` be a root of the monic polynomial
`f` of natural degree `n` with `f'(y₀)` a unit and `(bA j) y₀ⁱ` linearly independent over `K`.
Then there is an open set `U` of coefficient coordinates containing those of `f` such that every
monic `g` of natural degree `n` with `g_{n-i} = (-1)ⁿ ζ cA(g_i)` and coordinates in `U` has a root
`y` with `y σ(y) = 1` and `(bA j) yⁱ` linearly independent over `K`. -/
theorem exists_unitary_root_nhds (bA : Module.Basis ι K A) (cA : A →+* A) (ζ : A)
    (σ : S →ₐ[K] S) (hσ : ∀ a, σ (algebraMap A S a) = algebraMap A S (cA a))
    {n : ℕ} (y₀ : S) (f : A[X]) (hy₀ : y₀ * σ y₀ = 1) (hfm : f.Monic) (hfd : f.natDegree = n)
    (hf₀ : aeval y₀ f = 0) (hf' : IsUnit (aeval y₀ (derivative f)))
    (hind : LinearIndependent K
      (fun ji : ι × Fin n => algebraMap A S (bA ji.1) * y₀ ^ (ji.2 : ℕ))) :
    ∃ U : Set (Fin n → ι → K), IsOpen U ∧
      (fun (i : Fin n) (j : ι) => bA.repr (f.coeff i) j) ∈ U ∧
      ∀ g : A[X], g.Monic → g.natDegree = n →
        (∀ i ≤ n, g.coeff (n - i) = (-1) ^ n * ζ * cA (g.coeff i)) →
        (fun (i : Fin n) (j : ι) => bA.repr (g.coeff i) j) ∈ U →
        ∃ y : S, y * σ y = 1 ∧ aeval y g = 0 ∧
          LinearIndependent K
            (fun ji : ι × Fin n => algebraMap A S (bA ji.1) * y ^ (ji.2 : ℕ)) := by
  classical
  let bS := Module.finBasis K S
  let m := Module.finrank K S
  let : NormedRing (Matrix (Fin m) (Fin m) K) := Matrix.linftyOpNormedRing
  let : NormedAlgebra K (Matrix (Fin m) (Fin m) K) := Matrix.linftyOpNormedAlgebra
  let : NormedCommRing S := NormedCommRing.induced S (Matrix (Fin m) (Fin m) K)
    (Algebra.leftMulMatrix bS) (Algebra.leftMulMatrix_injective bS)
  let : NormedAlgebra K S := NormedAlgebra.induced K S (Matrix (Fin m) (Fin m) K)
    (Algebra.leftMulMatrix bS)
  have : CompleteSpace S := FiniteDimensional.complete K S
  let P := Fin n → ι → K
  let L : Fin n → P →L[K] S := fun i => ∑ j : ι,
    ((ContinuousLinearMap.proj (R := K) j : (ι → K) →L[K] K).comp
      (ContinuousLinearMap.proj (R := K) i : P →L[K] (ι → K))).smulRight
      (algebraMap A S (bA j))
  have hL (g : A[X]) (i : Fin n) :
      L i (fun (i : Fin n) (j : ι) => bA.repr (g.coeff i) j) = algebraMap A S (g.coeff i) := by
    conv_rhs => rw [← bA.sum_repr (g.coeff i)]
    simp [L, map_sum, Algebra.smul_def, IsScalarTower.algebraMap_apply K A S]
    rfl
  have hG (g : A[X]) (hgm : g.Monic) (hgd : g.natDegree = n) (y : S) :
      y ^ n + ∑ i : Fin n, L i (fun (i : Fin n) (j : ι) => bA.repr (g.coeff i) j) * y ^ (i : ℕ) =
        aeval y g := by
    rw [aeval_monic_eq hgm hgd]
    simp only [hL]
  let p₀ : P := fun (i : Fin n) (j : ι) => bA.repr (f.coeff i) j
  have h₀ : y₀ ^ n + ∑ i : Fin n, L i p₀ * y₀ ^ (i : ℕ) = 0 := by
    rw [hG f hfm hfd, hf₀]
  have hu : IsUnit ((n : S) * y₀ ^ (n - 1) +
      ∑ i : Fin n, L i p₀ * ((i : ℕ) * y₀ ^ ((i : ℕ) - 1))) := by
    simp only [p₀, hL]
    rw [← aeval_derivative_monic_eq hfm hfd]
    exact hf'
  obtain ⟨N₀, hN₀, V₀, hV₀, huniq, hex⟩ := exists_root_nhds L y₀ p₀ h₀ hu
  have hσc : Continuous σ := LinearMap.continuous_of_finiteDimensional σ.toLinearMap
  have hσy₀ : σ y₀ * y₀ = 1 := by rw [mul_comm]; exact hy₀
  let w₀ : Sˣ := ⟨σ y₀, y₀, hσy₀, hy₀⟩
  have hρ : ContinuousAt (fun y => Ring.inverse (σ y)) y₀ :=
    (NormedRing.inverse_continuousAt w₀).comp_of_eq hσc.continuousAt rfl
  have hρy₀ : Ring.inverse (σ y₀) = y₀ := by
    rw [show σ y₀ = (w₀ : S) from rfl, Ring.inverse_unit]
    rfl
  have hU1 : {y | IsUnit (σ y)} ∈ 𝓝 y₀ :=
    hσc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds ⟨w₀, rfl⟩)
  have hU2 : {y | Ring.inverse (σ y) ∈ N₀} ∈ 𝓝 y₀ :=
    hρ.preimage_mem_nhds (by rw [hρy₀]; exact hN₀)
  have hU3 : {y | LinearIndependent K
      (fun ji : ι × Fin n => algebraMap A S (bA ji.1) * y ^ (ji.2 : ℕ))} ∈ 𝓝 y₀ := by
    have hc : Continuous (fun y : S =>
        fun ji : ι × Fin n => algebraMap A S (bA ji.1) * y ^ (ji.2 : ℕ)) := by
      fun_prop
    exact hc.continuousAt.preimage_mem_nhds hind.eventually
  let N₁ := N₀ ∩ {y | IsUnit (σ y)} ∩ {y | Ring.inverse (σ y) ∈ N₀} ∩
    {y | LinearIndependent K
      (fun ji : ι × Fin n => algebraMap A S (bA ji.1) * y ^ (ji.2 : ℕ))}
  have hN₁ : N₁ ∈ 𝓝 y₀ := inter_mem (inter_mem (inter_mem hN₀ hU1) hU2) hU3
  have hev : ∀ᶠ p in 𝓝 p₀, p ∈ V₀ ∧ ∃ y ∈ N₁, y ^ n + ∑ i : Fin n, L i p * y ^ (i : ℕ) = 0 :=
    (Filter.eventually_mem_set.mpr hV₀).and (hex N₁ hN₁)
  obtain ⟨U, hUsub, hUo, hp₀U⟩ := mem_nhds_iff.mp hev
  refine ⟨U, hUo, hp₀U, ?_⟩
  intro g hgm hgd hgc hgU
  obtain ⟨hpV, y, ⟨⟨⟨hyN₀, hyu⟩, hyρ⟩, hyind⟩, hyroot⟩ := hUsub hgU
  rw [hG g hgm hgd] at hyroot
  obtain ⟨w, hw⟩ := hyu
  have hσg : aeval (w : S) (g.map cA) = 0 := by
    rw [hw, aeval_def, eval₂_map]
    have hcomp : (algebraMap A S).comp cA = (σ : S →+* S).comp (algebraMap A S) := by
      ext a
      simp [hσ]
    rw [hcomp]
    change eval₂ ((σ : S →+* S).comp (algebraMap A S)) ((σ : S →+* S) y) g = 0
    rw [← hom_eval₂, ← aeval_def, hyroot, map_zero]
  have hroot' : aeval ((w⁻¹ : Sˣ) : S) g = 0 :=
    aeval_inv_eq_zero_of_reflect w hgd.le (reflect_eq_of_conjRecip cA ζ hgd.le hgc) hσg
  have hinvw : Ring.inverse (σ y) = ((w⁻¹ : Sˣ) : S) := by rw [← hw, Ring.inverse_unit]
  have hyN₀' : ((w⁻¹ : Sˣ) : S) ∈ N₀ := hinvw ▸ hyρ
  have heq : y = ((w⁻¹ : Sˣ) : S) := huniq _ hpV y hyN₀ _ hyN₀'
    (by rw [hG g hgm hgd]; exact hyroot) (by rw [hG g hgm hgd]; exact hroot')
  refine ⟨y, ?_, hyroot, hyind⟩
  rw [← hw, heq]
  exact w.inv_mul

end UnitaryRoot

section LinearIndependence

variable {K A S : Type*} [Field K] [CommRing A] [Algebra K A] [CommRing S] [Algebra A S]
  {ι : Type*} [Fintype ι]

/-- Linear independence over `K` of the elements `(bA j) yⁱ` gives linear independence of
`1, y, …, y^{n-1}` over `A`. -/
theorem eq_zero_of_linearIndependent (bA : Module.Basis ι K A) [Algebra K S]
    [IsScalarTower K A S] {n : ℕ} {y : S}
    (hy : LinearIndependent K
      (fun ji : ι × Fin n => algebraMap A S (bA ji.1) * y ^ (ji.2 : ℕ)))
    (c : Fin n → A) (hc : ∑ i, algebraMap A S (c i) * y ^ (i : ℕ) = 0) : c = 0 := by
  classical
  rw [Fintype.linearIndependent_iff] at hy
  have h := hy (fun ji => bA.repr (c ji.2) ji.1) (by
    rw [Fintype.sum_prod_type_right]
    conv_rhs => rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← bA.sum_repr (c i)]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      mul_assoc])
  funext i
  rw [← bA.sum_repr (c i)]
  simp [fun j => h (j, i)]

end LinearIndependence

section TensorFacts

variable {F E B : Type*} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  (K : Type*) [Field K] [Algebra F K]

/-- The map `ψ = id ⊗ (E → B) : K ⊗[F] E → K ⊗[F] B`. -/
abbrev psi (F E B K : Type*) [Field F] [Field E] [Algebra F E] [Ring B] [Algebra E B]
    [Algebra F B] [IsScalarTower F E B] [Field K] [Algebra F K] : K ⊗[F] E →ₐ[K] K ⊗[F] B :=
  Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F E B)

/-- The image of `ψ` is central. -/
theorem psi_commute (a : K ⊗[F] E) (r : K ⊗[F] B) : Commute (psi F E B K a) r := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => rw [map_add]; exact ha.add_left ha'
  | tmul k e =>
    induction r using TensorProduct.inductionOn with
    | add r r' hr hr' => exact hr.add_right hr'
    | tmul k' b' =>
      simp only [psi, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        IsScalarTower.coe_toAlgHom']
      change (k ⊗ₜ[F] algebraMap E B e) * (k' ⊗ₜ[F] b') =
        (k' ⊗ₜ[F] b') * (k ⊗ₜ[F] algebraMap E B e)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm k k',
        Algebra.commutes]

variable (cE : E ≃ₐ[F] E)

/-- The map `id ⊗ c : K ⊗[F] E → K ⊗[F] E` induced by an automorphism `c` of `E/F`. -/
abbrev conjA : K ⊗[F] E →ₐ[K] K ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id K K) cE.toAlgHom

/-- `id ⊗ c` is an involution when `c` is. -/
theorem conjA_conjA (hcE : Function.Involutive cE) (a : K ⊗[F] E) :
    conjA K cE (conjA K cE a) = a := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => rw [map_add, map_add, ha, ha']
  | tmul k e => simp [conjA, hcE e]

/-- `τ_v ∘ ψ = ψ ∘ (id ⊗ c)` when `τ` acts on `E` by `c`. -/
theorem baseChange_psi (τ : FirstKindInvolution F B)
    (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (cE e)) (a : K ⊗[F] E) :
    τ.baseChange K (psi F E B K a) = psi F E B K (conjA K cE a) := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => rw [map_add, FirstKindInvolution.map_add, ha, ha', map_add, map_add]
  | tmul k e =>
    simp only [psi, conjA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      IsScalarTower.coe_toAlgHom', FirstKindInvolution.baseChange_tmul]
    rw [hτ]
    rfl

/-- An anti-automorphism preserves powers. -/
theorem baseChange_pow (τ : FirstKindInvolution F B) (r : K ⊗[F] B) (k : ℕ) :
    τ.baseChange K (r ^ k) = (τ.baseChange K r) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, FirstKindInvolution.map_mul, ih, pow_succ']

/-- `τ_v (p(r)) = p^c(τ_v r)`, polynomials being evaluated through `ψ`. -/
theorem baseChange_eval₂ (τ : FirstKindInvolution F B)
    (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (cE e)) (r : K ⊗[F] B)
    (p : (K ⊗[F] E)[X]) :
    τ.baseChange K (p.eval₂ (psi F E B K : K ⊗[F] E →+* K ⊗[F] B) r) =
      p.eval₂ ((psi F E B K : K ⊗[F] E →+* K ⊗[F] B).comp (conjA K cE : K ⊗[F] E →+* K ⊗[F] E))
        (τ.baseChange K r) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add, FirstKindInvolution.map_add, hp, hq, eval₂_add]
  | monomial k a =>
    rw [eval₂_monomial, eval₂_monomial, FirstKindInvolution.map_mul, baseChange_pow]
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [baseChange_psi K cE τ hτ]
    exact ((psi_commute K _ _).eq).symm

end TensorFacts

section Local

variable {F E B : Type*} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]

/-- **The unitary Krasner lemma over a complete nontrivially normed field `K`.** This is the
statement `NumberFieldUnitaryLocalRootNeighborhoodStatement` with `F_v` replaced by any complete
nontrivially normed field `K` that is an `F`-algebra and `conjugation F E` by any involutive
automorphism `cE` of `E/F` through which `τ` acts on `E`. -/
theorem local_root_neighborhood (τ : FirstKindInvolution F B) (cE : E ≃ₐ[F] E)
    (hcE : Function.Involutive cE)
    (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (cE e))
    (n : ℕ) (z : E) (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K]
    (b : Module.Basis (Fin 2) F E) (x : K ⊗[F] B) (f : (K ⊗[F] E)[X])
    (hx : x * τ.baseChange K x = 1) (hfm : f.Monic) (hfd : f.natDegree = n)
    (hfc : ∀ i ≤ n, f.coeff (n - i) = (-1) ^ n * ((1 : K) ⊗ₜ[F] z) * conjA K cE (f.coeff i))
    (hf0 : f.eval₂ (psi F E B K : K ⊗[F] E →+* K ⊗[F] B) x = 0)
    (hf' : IsUnit ((derivative f).eval₂ (psi F E B K : K ⊗[F] E →+* K ⊗[F] B) x))
    (hind : ∀ c : Fin n → K ⊗[F] E, ∑ i, psi F E B K (c i) * x ^ (i : ℕ) = 0 → c = 0) :
    ∃ U : Set (Fin n → Fin 2 → K), IsOpen U ∧
      (fun (i : Fin n) (j : Fin 2) => (Algebra.TensorProduct.basis K b).repr (f.coeff i) j) ∈ U ∧
      ∀ g : (K ⊗[F] E)[X], g.Monic → g.natDegree = n →
        (∀ i ≤ n, g.coeff (n - i) = (-1) ^ n * ((1 : K) ⊗ₜ[F] z) * conjA K cE (g.coeff i)) →
        (fun (i : Fin n) (j : Fin 2) => (Algebra.TensorProduct.basis K b).repr (g.coeff i) j) ∈
          U →
        ∃ y : K ⊗[F] B, y * τ.baseChange K y = 1 ∧
          g.eval₂ (psi F E B K : K ⊗[F] E →+* K ⊗[F] B) y = 0 ∧
          ∀ c : Fin n → K ⊗[F] E, ∑ i, psi F E B K (c i) * y ^ (i : ℕ) = 0 → c = 0 := by
  classical
  subst hfd
  let ψ : K ⊗[F] E →+* K ⊗[F] B := psi F E B K
  let cA : K ⊗[F] E →+* K ⊗[F] E := conjA K cE
  let ζ : K ⊗[F] E := (1 : K) ⊗ₜ[F] z
  let bA := Algebra.TensorProduct.basis K b
  have hcomm : ∀ a, Commute (ψ a) x := fun a => psi_commute K a x
  let φ : AdjoinRoot f →+* K ⊗[F] B := Ideal.Quotient.lift (Ideal.span {f})
    (eval₂RingHom' ψ x hcomm) (fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      change _ * f.eval₂ ψ x = 0
      rw [hf0, mul_zero])
  have hφmk : ∀ p : (K ⊗[F] E)[X], φ (AdjoinRoot.mk f p) = p.eval₂ ψ x := fun p => rfl
  have hφalg : ∀ a, φ (algebraMap (K ⊗[F] E) (AdjoinRoot f) a) = ψ a := fun a => by
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, hφmk, eval₂_C]
  have hφcomp : φ.comp (algebraMap (K ⊗[F] E) (AdjoinRoot f)) = ψ := RingHom.ext hφalg
  have hφroot : φ (AdjoinRoot.root f) = x := by rw [AdjoinRoot.root, hφmk, eval₂_X]
  have hφaeval : ∀ (s : AdjoinRoot f) (p : (K ⊗[F] E)[X]), φ (aeval s p) = p.eval₂ ψ (φ s) :=
    fun s p => by rw [aeval_def, hom_eval₂, hφcomp]
  let bS : Module.Basis (Fin f.natDegree) (K ⊗[F] E) (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis' hfm).basis
  have hbS : ∀ i, bS i = AdjoinRoot.root f ^ (i : ℕ) := fun i =>
    congrFun (PowerBasis.coe_basis (AdjoinRoot.powerBasis' hfm)) i
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have hsum := bS.sum_repr s
    have hc : bS.repr s = 0 := by
      have h := hind (fun i => bS.repr s i) (by
        rw [← hs]
        conv_rhs => rw [← hsum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_mul, hφalg, hbS, map_pow, hφroot]
        rfl)
      refine Finsupp.ext fun i => ?_
      simpa only [Finsupp.coe_zero, Pi.zero_apply] using congrFun h i
    exact (LinearEquiv.map_eq_zero_iff _).mp hc
  have hroot0 : aeval (AdjoinRoot.root f) f = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hζ : ζ * ((-1) ^ f.natDegree * cA (f.coeff 0)) = 1 := by
    have h := hfc 0 (Nat.zero_le _)
    rw [Nat.sub_zero, hfm.coeff_natDegree] at h
    have e : ζ * ((-1) ^ f.natDegree * cA (f.coeff 0)) =
        (-1) ^ f.natDegree * ζ * cA (f.coeff 0) := by ring
    rw [e]
    exact h.symm
  have hf0c : f.coeff 0 = (-1) ^ f.natDegree * ζ := by
    have h := hfc f.natDegree le_rfl
    rw [Nat.sub_self, hfm.coeff_natDegree, map_one, mul_one] at h
    exact h
  have hunit0 : IsUnit (f.coeff 0) := by
    rw [hf0c]
    exact (isUnit_neg_one.pow _).mul (IsUnit.of_mul_eq_one _ hζ)
  obtain ⟨u0, hu0⟩ := hunit0
  have hXmul : AdjoinRoot.root f * (algebraMap (K ⊗[F] E) (AdjoinRoot f) (-↑u0⁻¹) *
      aeval (AdjoinRoot.root f) (divX f)) = 1 := by
    have h := congrArg (aeval (AdjoinRoot.root f)) (X_mul_divX_add f)
    rw [map_add, map_mul, aeval_X, aeval_C, hroot0, ← hu0] at h
    calc AdjoinRoot.root f * (algebraMap (K ⊗[F] E) (AdjoinRoot f) (-↑u0⁻¹) *
          aeval (AdjoinRoot.root f) (divX f))
        = algebraMap (K ⊗[F] E) (AdjoinRoot f) (-↑u0⁻¹) *
          (AdjoinRoot.root f * aeval (AdjoinRoot.root f) (divX f)) := by ring
      _ = algebraMap (K ⊗[F] E) (AdjoinRoot f) (-↑u0⁻¹) *
          (-algebraMap (K ⊗[F] E) (AdjoinRoot f) ↑u0) := by
          rw [eq_neg_of_add_eq_zero_left h]
      _ = algebraMap (K ⊗[F] E) (AdjoinRoot f) (↑u0⁻¹ * ↑u0) := by
          rw [map_neg, map_mul]
          ring
      _ = 1 := by simp
  have hXunit : IsUnit (AdjoinRoot.root f) := IsUnit.of_mul_eq_one _ hXmul
  let Xu := hXunit.unit
  have hconjf : ∀ i ≤ f.natDegree, (f.map cA).coeff (f.natDegree - i) =
      (-1) ^ f.natDegree * cA ζ * cA ((f.map cA).coeff i) := by
    intro i hi
    rw [coeff_map, coeff_map, hfc i hi, map_mul, map_mul, map_pow, map_neg, map_one]
    rfl
  have hmapmap : (f.map cA).map cA = f := by
    rw [Polynomial.map_map]
    ext i
    rw [coeff_map]
    exact conjA_conjA K cE hcE _
  have hrefl : reflect f.natDegree (f.map cA) = C ((-1) ^ f.natDegree * cA ζ) * f := by
    rw [reflect_eq_of_conjRecip cA (cA ζ) natDegree_map_le hconjf, hmapmap]
  have hσroot : f.eval₂ ((algebraMap (K ⊗[F] E) (AdjoinRoot f)).comp cA)
      ((Xu⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) = 0 := by
    rw [← eval₂_map, ← aeval_def]
    exact aeval_inv_eq_zero_of_reflect Xu natDegree_map_le hrefl
      (by rw [IsUnit.unit_spec]; exact hroot0)
  let σ₀ : AdjoinRoot f →+* AdjoinRoot f :=
    AdjoinRoot.lift ((algebraMap (K ⊗[F] E) (AdjoinRoot f)).comp cA) _ hσroot
  have hσ₀alg : ∀ a, σ₀ (algebraMap (K ⊗[F] E) (AdjoinRoot f) a) =
      algebraMap (K ⊗[F] E) (AdjoinRoot f) (cA a) := fun a => by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.lift_of hσroot
  let σ : AdjoinRoot f →ₐ[K] AdjoinRoot f :=
    { σ₀ with
      commutes' := fun k => by
        change σ₀ (algebraMap K (AdjoinRoot f) k) = algebraMap K (AdjoinRoot f) k
        rw [IsScalarTower.algebraMap_apply K (K ⊗[F] E) (AdjoinRoot f), hσ₀alg]
        congr 1
        exact (conjA K cE).commutes k }
  have hσalg : ∀ a, σ (algebraMap (K ⊗[F] E) (AdjoinRoot f) a) =
      algebraMap (K ⊗[F] E) (AdjoinRoot f) (cA a) := hσ₀alg
  have hσroot' : σ (AdjoinRoot.root f) = ((Xu⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) :=
    AdjoinRoot.lift_root hσroot
  have hy₀ : AdjoinRoot.root f * σ (AdjoinRoot.root f) = 1 := by
    rw [hσroot']
    conv_lhs => rw [← hXunit.unit_spec]
    exact Xu.mul_inv
  have hτx : τ.baseChange K x = φ ((Xu⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) := by
    have h1 : φ ((Xu⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) * x = 1 := by
      rw [← hφroot, ← map_mul]
      conv_lhs => rw [← hXunit.unit_spec]
      rw [Xu.inv_mul, map_one]
    calc τ.baseChange K x = (φ ((Xu⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) * x) *
          τ.baseChange K x := by rw [h1, one_mul]
      _ = φ ((Xu⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) := by rw [mul_assoc, hx, mul_one]
  have hφσ : ∀ s, τ.baseChange K (φ s) = φ (σ s) := fun s => by
    induction s using AdjoinRoot.induction_on with
    | ih p =>
      rw [hφmk, baseChange_eval₂ K cE τ hτ, hτx]
      change _ = φ (σ₀ (AdjoinRoot.mk f p))
      rw [AdjoinRoot.lift_mk, hom_eval₂, ← RingHom.comp_assoc, hφcomp]
  have : FiniteDimensional K (K ⊗[F] E) := Module.Finite.of_basis bA
  have : Module.Finite (K ⊗[F] E) (AdjoinRoot f) := hfm.finite_adjoinRoot
  have : FiniteDimensional K (AdjoinRoot f) := Module.Finite.trans (K ⊗[F] E) (AdjoinRoot f)
  have hf'S : IsUnit (aeval (AdjoinRoot.root f) (derivative f)) := by
    have hφu : IsUnit (φ (aeval (AdjoinRoot.root f) (derivative f))) := by
      rw [hφaeval, hφroot]
      exact hf'
    have hinj : Function.Injective
        (LinearMap.mulLeft K (aeval (AdjoinRoot.root f) (derivative f))) := by
      rw [injective_iff_map_eq_zero]
      intro s hs
      apply hφinj
      rw [map_zero]
      rw [LinearMap.mulLeft_apply] at hs
      have h2 : φ (aeval (AdjoinRoot.root f) (derivative f)) * φ s = 0 := by
        rw [← map_mul, hs, map_zero]
      exact hφu.mul_right_eq_zero.mp h2
    obtain ⟨t, ht⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
    exact IsUnit.of_mul_eq_one t ht
  have hind₀ : LinearIndependent K (fun ji : Fin 2 × Fin f.natDegree =>
      algebraMap (K ⊗[F] E) (AdjoinRoot f) (bA ji.1) * AdjoinRoot.root f ^ (ji.2 : ℕ)) := by
    have h := (bA.smulTower bS).linearIndependent
    have e : ⇑(bA.smulTower bS) = fun ji : Fin 2 × Fin f.natDegree =>
        algebraMap (K ⊗[F] E) (AdjoinRoot f) (bA ji.1) * AdjoinRoot.root f ^ (ji.2 : ℕ) := by
      funext ji
      rw [Module.Basis.smulTower_apply, hbS, Algebra.smul_def]
    rwa [e] at h
  obtain ⟨U, hUo, hfU, hU⟩ := exists_unitary_root_nhds (K := K) (A := K ⊗[F] E)
    (S := AdjoinRoot f) bA cA ζ σ hσalg (AdjoinRoot.root f) f hy₀ hfm rfl hroot0 hf'S hind₀
  refine ⟨U, hUo, hfU, fun g hgm hgd hgc hgU => ?_⟩
  obtain ⟨y, hyσ, hyg, hyind⟩ := hU g hgm hgd hgc hgU
  refine ⟨φ y, ?_, ?_, ?_⟩
  · rw [hφσ, ← map_mul, hyσ, map_one]
  · change g.eval₂ ψ (φ y) = 0
    rw [← hφaeval, hyg, map_zero]
  · intro c hc
    apply eq_zero_of_linearIndependent bA hyind c
    apply hφinj
    rw [map_zero, ← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφalg, map_pow]
    rfl

end Local

end Langlands.CentralSimple.UnitaryKrasner

namespace Langlands.CentralSimple

open UnitaryKrasner Langlands.GroupScheme.SU3Root NumberField

universe u

/-- **Unitary roots of nearby conjugate-reciprocal polynomials (unitary Krasner lemma).** -/
theorem numberFieldUnitaryLocalRootNeighborhood :
    NumberFieldUnitaryLocalRootNeighborhoodStatement.{u} := by
  intro F E B _ _ _ _ _ _ _ _ _ _ _ _ _ τ hτ n _ z v b x f hx hfm hfd hfc hf0 hf' hind
  rcases v with w | v
  · let : NontriviallyNormedField w.Completion :=
      Global.AdelicSpaceLocalFields.infiniteNormedField F w
    exact local_root_neighborhood τ (conjugation F E) (conjugation_involutive F E) hτ n z
      w.Completion b x f hx hfm hfd hfc hf0 hf' hind
  · let : NontriviallyNormedField (v.adicCompletion F) :=
      Global.AdelicSpaceLocalFields.normedField (𝓞 F) F v
    have : CompleteSpace (v.adicCompletion F) :=
      Global.AdelicSpaceLocalFields.completeSpace (𝓞 F) F v
    exact local_root_neighborhood τ (conjugation F E) (conjugation_involutive F E) hτ n z
      (v.adicCompletion F) b x f hx hfm hfd hfc hf0 hf' hind

end Langlands.CentralSimple
