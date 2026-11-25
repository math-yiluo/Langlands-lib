/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Basic
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Algebra.Central.ReducedNorm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `Cᵣ` fields

A field `K` has *property `Cᵣ`* if every homogeneous form of degree `d > 0` in more than
`d ^ r` variables has a nontrivial zero over `K`. The case `r = 1` is *quasi-algebraic
closure*.

## Main definitions

- `IsCField`: the class of fields with property `Cᵣ`.
- `IsQuasiAlgClosed`: quasi-algebraically closed fields, that is, `C₁` fields.

## Main statements

- `IsCField.mono`: property `Cᵣ` implies property `Cₛ` for `r ≤ s`.
- `IsAlgClosed.isCField_zero`: an algebraically closed field is `C₀`, hence `C₁`.
- `IsQuasiAlgClosed.of_finiteDimensional`: a finite extension of a `C₁` field is `C₁`.
- `IsQuasiAlgClosed.of_isAlgebraic`: an algebraic extension of a `C₁` field is `C₁`.
- `IsQuasiAlgClosed.finrank_eq_one_of_isCentral`: a central division algebra over a `C₁` field
  is trivial.
- `IsQuasiAlgClosed.subsingleton_brauerGroup`: the Brauer group of a `C₁` field vanishes.

## Implementation notes

The variables are indexed by `Fin N` rather than by an arbitrary finite type: a class field
quantifying over `σ : Type v` would make `IsCField` carry a second universe parameter, which
every use site would then have to disambiguate.
-/

@[expose] public section

universe u

open MvPolynomial

/-- Let `r ≥ 0`. A field `K` has *property `Cᵣ`* if every homogeneous polynomial form
`F ∈ K[x₁, …, x_N]` of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero in
`K ^ N`, that is, there is `x : Fin N → K` with `x ≠ 0` and `F(x) = 0`.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
class IsCField (K : Type*) [Field K] (r : ℕ) : Prop where
  /-- A homogeneous form of degree `d > 0` in `N > d ^ r` variables has a nontrivial zero. -/
  exists_ne_zero_and_eval_eq_zero {N d : ℕ} (F : MvPolynomial (Fin N) K)
    (hF : F.IsHomogeneous d) (hd : 0 < d) (hN : d ^ r < N) :
    ∃ x : Fin N → K, x ≠ 0 ∧ eval x F = 0

/-- A field is *quasi-algebraically closed* if it is `C₁`: every homogeneous form of degree
`d > 0` in `N > d` variables has a nontrivial zero. -/
abbrev IsQuasiAlgClosed (K : Type*) [Field K] : Prop := IsCField K 1

variable {K : Type*} [Field K]

/-- Property `Cᵣ` implies property `Cₛ` for `r ≤ s`. -/
theorem IsCField.mono {r s : ℕ} (hrs : r ≤ s) [h : IsCField K r] : IsCField K s where
  exists_ne_zero_and_eval_eq_zero F hF hd hN :=
    h.exists_ne_zero_and_eval_eq_zero F hF hd ((Nat.pow_le_pow_right hd hrs).trans_lt hN)

/-- An algebraically closed field is `C₀`: a homogeneous form of positive degree in at least two
variables has a nontrivial zero.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
instance IsAlgClosed.isCField_zero [IsAlgClosed K] : IsCField K 0 where
  exists_ne_zero_and_eval_eq_zero {N d} F hF hd hN := by
    rw [pow_zero] at hN
    let i₀ : Fin N := ⟨0, by omega⟩
    let i₁ : Fin N := ⟨1, hN⟩
    have h₀₁ : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
    -- the point `(a, b, 0, …, 0)` and the restrictions of `F` to two affine lines through it
    let v : K → K → Fin N → K := fun a b i =>
      if i = i₀ then a else if i = i₁ then b else 0
    have hv₀ (a b : K) : v a b i₀ = a := by simp [v]
    have hv₁ (a b : K) : v a b i₁ = b := by simp [v, h₀₁]
    have heval (g : Fin N → Polynomial K) (t : K) :
        (aeval g F).eval t = eval (fun i => (g i).eval t) F := by
      rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
      rfl
    let p : Polynomial K :=
      aeval (fun i => if i = i₀ then 1 else if i = i₁ then Polynomial.X else 0) F
    let q : Polynomial K :=
      aeval (fun i => if i = i₀ then Polynomial.X else if i = i₁ then 1 else 0) F
    have hp (t : K) : p.eval t = eval (v 1 t) F := by
      rw [heval]
      exact congrArg (fun x => eval x F) (funext fun i => by simp only [v]; split_ifs <;> simp)
    have hq (t : K) : q.eval t = eval (v t 1) F := by
      rw [heval]
      exact congrArg (fun x => eval x F) (funext fun i => by simp only [v]; split_ifs <;> simp)
    by_cases hroot : ∃ t, p.IsRoot t
    · obtain ⟨t, ht⟩ := hroot
      refine ⟨v 1 t, fun h => by simpa [hv₀] using congrFun h i₀, ?_⟩
      rw [← hp]
      exact ht
    -- otherwise `F (1, t, 0, …, 0)` is a constant `c`, so `F (s, 1, 0, …, 0) = c * s ^ d`
    push Not at hroot
    have hdeg : p.degree = 0 := by
      by_contra h
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p h
      exact hroot t ht
    obtain ⟨c, hc⟩ : ∃ c, p = Polynomial.C c :=
      ⟨_, Polynomial.eq_C_of_degree_eq_zero hdeg⟩
    have hqeq : q = Polynomial.C c * Polynomial.X ^ d := by
      refine Polynomial.eq_of_infinite_eval_eq _ _
        ((Set.finite_singleton (0 : K)).infinite_compl.mono fun s (hs : s ≠ 0) => ?_)
      have hvs : v s 1 = fun i => s * v 1 s⁻¹ i := by
        ext i; simp only [v]; split_ifs <;> simp [hs]
      have hFs : eval (fun i => s * v 1 s⁻¹ i) F = s ^ d * eval (v 1 s⁻¹) F :=
        hF.eval₂Hom_const_mul (RingHom.id K) s _
      rw [Set.mem_ofPred_eq, hq, hvs, hFs, ← hp, hc]
      simp only [Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      ring
    refine ⟨v 0 1, fun h => by simpa [hv₁] using congrFun h i₁, ?_⟩
    rw [← hq, hqeq]
    simp [hd.ne']

/-- An algebraically closed field is quasi-algebraically closed, since `C₀` implies `C₁`.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
instance IsAlgClosed.isQuasiAlgClosed [IsAlgClosed K] : IsQuasiAlgClosed K :=
  IsCField.mono zero_le_one

/-- Property `Cᵣ` for forms in variables indexed by an arbitrary finite type: a homogeneous form
of degree `d > 0` in more than `d ^ r` variables has a nontrivial zero. -/
theorem IsCField.exists_ne_zero_and_eval_eq_zero_of_finite {r : ℕ} [IsCField K r] {σ : Type*}
    [Finite σ] {d : ℕ} (F : MvPolynomial σ K) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (hN : d ^ r < Nat.card σ) : ∃ x : σ → K, x ≠ 0 ∧ eval x F = 0 := by
  let e := Finite.equivFin σ
  obtain ⟨x, hx, hFx⟩ := IsCField.exists_ne_zero_and_eval_eq_zero (rename e F)
    (hF.rename_isHomogeneous) hd hN
  refine ⟨x ∘ e, fun h => hx (funext fun i => ?_), by rwa [eval_rename] at hFx⟩
  simpa using congrFun h (e.symm i)

/-- Property `Cᵣ` is invariant under isomorphisms of fields. -/
theorem IsCField.of_ringEquiv {L : Type*} [Field L] {r : ℕ} (e : K ≃+* L) [IsCField K r] :
    IsCField L r where
  exists_ne_zero_and_eval_eq_zero F hF hd hN := by
    obtain ⟨x, hx, hFx⟩ := IsCField.exists_ne_zero_and_eval_eq_zero (map e.symm.toRingHom F)
      (hF.map _) hd hN
    refine ⟨e ∘ x, fun h => hx (funext fun i => by simpa using congrFun h i), ?_⟩
    have hF' : F = map e.toRingHom (map e.symm.toRingHom F) := by
      rw [map_map]
      simp [map_id]
    have key := eval₂_comp_left e.toRingHom (RingHom.id K) x (map e.symm.toRingHom F)
    rw [RingHom.comp_id] at key
    rw [hF', eval_map, show (e ∘ x) = e.toRingHom ∘ x from rfl, ← key]
    exact (congrArg e.toRingHom hFx).trans (map_zero _)

/-- A finite extension of a quasi-algebraically closed field is quasi-algebraically closed: the
norm of a form of degree `d` in `N > d` variables over `L` is a form of degree `[L : K] d` in
`[L : K] N` variables over `K`, and it only vanishes where the original form does.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
@[stacks 03RC]
theorem IsQuasiAlgClosed.of_finiteDimensional (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsQuasiAlgClosed K] : IsQuasiAlgClosed L where
  exists_ne_zero_and_eval_eq_zero {N d} F hF hd hN := by
    classical
    rw [pow_one] at hN
    set m := Module.finrank K L
    let b := Module.finBasis K L
    -- the generic point `zᵢ = ∑ⱼ bⱼ yᵢⱼ` and the form `G(y) = F(z)` over `L`
    let z : Fin N → MvPolynomial (Fin N × Fin m) L := fun i => ∑ j, C (b j) * X (i, j)
    let G : MvPolynomial (Fin N × Fin m) L := aeval z F
    have hG : G.IsHomogeneous d := by
      have h := hF.aeval z fun i =>
        IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (b j) (i, j)
      rwa [one_mul] at h
    -- the matrix of multiplication by `G` in the basis `b`, a matrix of forms over `K`
    let f : Fin m → Fin m → L →ₗ[K] K := fun j k => (b.coord j).comp (LinearMap.mulRight K (b k))
    let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin N × Fin m) K) :=
      fun j k => ∑ s ∈ G.support, monomial s (f j k (G.coeff s))
    have hM : M.det.IsHomogeneous (m * d) := by
      simpa using IsHomogeneous.det fun j k => hG.sum_monomial_linearMap (f j k)
    have hm : 0 < m := Module.finrank_pos
    have hevalG (y : Fin N × Fin m → K) :
        eval (algebraMap K L ∘ y) G = eval (fun i => ∑ j, y (i, j) • b j) F := by
      rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
      change aeval _ (aeval z F) = aeval _ F
      rw [← AlgHom.comp_apply, comp_aeval]
      congr 2
      funext i
      simp only [z, map_sum, map_mul, Algebra.smul_def]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [aeval_X, Function.comp_apply, mul_comm]
        exact congrArg _ (eval₂_C _ _ _)
    have hevalM (y : Fin N × Fin m → K) :
        eval y M.det = Algebra.norm K (eval (fun i => ∑ j, y (i, j) • b j) F) := by
      rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
      congr 1
      ext j k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M]
      rw [eval_sum_monomial_linearMap, hevalG, Algebra.leftMulMatrix_apply,
        LinearMap.toMatrix_apply]
      simp [f]
    obtain ⟨y, hy, hMy⟩ := IsCField.exists_ne_zero_and_eval_eq_zero_of_finite (r := 1) M.det hM
      (Nat.mul_pos hm hd) (by simpa [mul_comm m] using Nat.mul_lt_mul_of_pos_right hN hm)
    rw [hevalM, Algebra.norm_eq_zero_iff] at hMy
    refine ⟨fun i => ∑ j, y (i, j) • b j, fun h => hy (funext fun ij => ?_), hMy⟩
    have := congrArg (fun v => b.repr v ij.2) (congrFun h ij.1)
    simpa [Finsupp.single_apply] using this

/-- An algebraic extension of a quasi-algebraically closed field is quasi-algebraically closed:
the finitely many coefficients of a form lie in a finite subextension. -/
theorem IsQuasiAlgClosed.of_isAlgebraic (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsQuasiAlgClosed K] : IsQuasiAlgClosed L where
  exists_ne_zero_and_eval_eq_zero {N d} F hF hd hN := by
    let E := IntermediateField.adjoin K (F.coeffs : Set L)
    have : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin
      fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have := IsQuasiAlgClosed.of_finiteDimensional K E
    obtain ⟨F', hF'⟩ : F ∈ Set.range (map (algebraMap E L)) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      exact ⟨⟨c, IntermediateField.subset_adjoin K _ hc⟩, rfl⟩
    obtain ⟨x, hx, hFx⟩ := IsCField.exists_ne_zero_and_eval_eq_zero F'
      ((hF' ▸ hF).of_map (algebraMap E L).injective) hd hN
    refine ⟨algebraMap E L ∘ x,
      fun h => hx (funext fun i => (algebraMap E L).injective (by simpa using congrFun h i)), ?_⟩
    have key := eval₂_comp_left (algebraMap E L) (RingHom.id E) x F'
    rw [RingHom.comp_id] at key
    rw [← hF', eval_map, ← key]
    exact (congrArg (algebraMap E L) hFx).trans (map_zero _)

/-- A finite-dimensional central division algebra over a quasi-algebraically closed field `K`
is `K` itself: its reduced norm is a form of degree `d` in `d ^ 2` variables without nontrivial
zero, so `d = 1`.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
theorem IsQuasiAlgClosed.finrank_eq_one_of_isCentral (K D : Type*) [Field K] [IsQuasiAlgClosed K]
    [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D] :
    Module.finrank K D = 1 := by
  obtain ⟨d, hd, hdim, P, hP, hP0⟩ := Algebra.IsCentral.exists_isHomogeneous_eval_ne_zero K D
  rcases Nat.lt_or_ge d 2 with h | h
  · rw [hdim, show d = 1 by omega, one_pow]
  · obtain ⟨y, hy, hPy⟩ := IsCField.exists_ne_zero_and_eval_eq_zero P hP hd
      (by rw [pow_one, hdim, sq]; exact lt_mul_left hd (by omega))
    exact absurd hPy (hP0 y hy)

/-- The Brauer group of a quasi-algebraically closed field vanishes: every central simple
algebra over `K` is a matrix algebra over `K`.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
theorem IsQuasiAlgClosed.subsingleton_brauerGroup (K : Type u) [Field K] [IsQuasiAlgClosed K] :
    Subsingleton (BrauerGroup.{u, u} K) := by
  let one : CSA.{u, u} K := ⟨.of K K⟩
  suffices h : ∀ A : CSA.{u, u} K, IsBrauerEquivalent A one by
    refine ⟨fun A B => ?_⟩
    induction A using Quotient.inductionOn
    induction B using Quotient.inductionOn
    exact Quotient.sound ((h _).trans (h _).symm)
  intro A
  have := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  have : Algebra.IsCentral K D := Algebra.IsCentral.of_algEquiv_matrix e
  let f : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D) <| by
    refine ⟨(algebraMap K D).injective, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (Algebra.ofId K D).toLinearMap)
      (by rw [Module.finrank_self, finrank_eq_one_of_isCentral K D])).mp
      (algebraMap K D).injective
  let u : A ≃ₐ[K] Matrix (Fin 1) (Fin 1) A :=
    AlgEquiv.ofBijective (Matrix.scalarAlgHom (Fin 1) K) ⟨fun a b h => by
      simpa using congrFun (congrFun h 0) 0, fun M => ⟨M 0 0, by
        ext i j
        simp [Subsingleton.elim i 0, Subsingleton.elim j 0]⟩⟩
  exact ⟨1, n, one_ne_zero, hn.ne, ⟨u.symm.trans (e.trans f.symm.mapMatrix)⟩⟩

