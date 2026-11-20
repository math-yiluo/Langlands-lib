import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Global.Factors.FiniteComparisonProof

/-!
# Reduction of Shahidi's boundary nonvanishing to one enlarged set of places

`CuspidalPairBoundaryNonvanishingStatement` (Shahidi 1981, Theorem 5.2) quantifies over every
finite set `S` of finite places containing both exceptional sets, and its second conjunct
over every meromorphic function represented by the partial Euler product. This module
proves that both quantifiers can be discharged formally:

* **uniqueness** (statement Markdown §2): two functions with `IsPartialPairLFunction` agree
  on a right half-plane, hence, by the identity theorem, in a punctured neighbourhood of
  every point, so they have the same `meromorphicOrderAt` everywhere;
* **enlargement of `S`** (statement Markdown §3): if `S ⊆ S₀` and `L₀` represents the partial
  Euler product outside `S₀`, then `L₀ · ∏_(v ∈ S₀ \ S) L(s, Π_v × Π'_v)` represents the partial
  Euler product outside `S`; each added factor is the reciprocal of the entire function
  `P_v(q_v^(-s))` with `P_v(0) = 1`, so it has nonpositive order everywhere and cannot create a
  zero.

Hence the target follows from `CuspidalPairBoundaryNonvanishingEnlargedStatement`: for every
admissible `S` there are a finite set `S₀ ⊇ S` and one representative `L₀` of the partial
L-function outside `S₀` with nonpositive order at every `1 + iy`. This is the form in which
Shahidi's proof (Sh81, pp. 351–353) gives the theorem, with `S₀` containing in addition the
finite places where the generic character `χ` of Sh81 Theorem 5.1 ramifies.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology Polynomial

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairFunctionalEquation
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CuspidalPairBoundaryNonvanishing

/-! ### Reciprocals of entire functions -/

/-- An entire function that does not vanish identically has finite order everywhere. -/
theorem meromorphicOrderAt_ne_top_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) (x : ℂ) : meromorphicOrderAt f x ≠ ⊤ := by
  have hmero : MeromorphicOn f Set.univ := fun z _ => (hf.analyticAt z).meromorphicAt
  have h0 : meromorphicOrderAt f z₀ ≠ ⊤ := by
    rw [(hf.analyticAt z₀).meromorphicOrderAt_eq,
      ((hf.analyticAt z₀).analyticOrderAt_eq_zero).mpr hz₀]
    simp
  exact hmero.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ z₀) (Set.mem_univ x) h0

/-- The reciprocal of an entire function that does not vanish identically has nonpositive
order everywhere. -/
theorem meromorphicOrderAt_inv_nonpos {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hz₀ : f z₀ ≠ 0) (x : ℂ) : meromorphicOrderAt (fun s => (f s)⁻¹) x ≤ 0 := by
  have hx := meromorphicOrderAt_ne_top_of_differentiable hf hz₀ x
  have hnn : 0 ≤ meromorphicOrderAt f x := (hf.analyticAt x).meromorphicOrderAt_nonneg
  have e : (fun s => (f s)⁻¹) = f⁻¹ := rfl
  rw [e, meromorphicOrderAt_inv]
  lift meromorphicOrderAt f x to ℤ using hx with m hm
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hnn
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact_mod_cast neg_nonpos.mpr hm0

/-- `s ↦ Q(q^(-s))` is entire for `q > 0`. -/
theorem differentiable_eval_spectralPoint (Q : ℂ[X]) {q : ℕ} (hq : 0 < q) :
    Differentiable ℂ (fun s => Q.eval (RankinSelberg.spectralPoint q s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h1 : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (-s)) := fun s =>
    (differentiableAt_id.neg).const_cpow (Or.inl hq0)
  exact Q.differentiable.comp h1

/-- If `Q(0) = 1` and `q > 1`, then `s ↦ Q(q^(-s))` does not vanish identically: it is
nonzero at `s = n` for large natural `n`, where `q^(-n)` is close to `0`. -/
theorem exists_eval_spectralPoint_ne_zero {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) {q : ℕ}
    (hq : 1 < q) : ∃ s : ℂ, Q.eval (RankinSelberg.spectralPoint q s) ≠ 0 := by
  have hnorm : ‖(q : ℂ)⁻¹‖ < 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)
  have ht : Tendsto (fun n : ℕ => ((q : ℂ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hP0 : ∀ᶠ x in 𝓝 (0 : ℂ), Q.eval x ≠ 0 := by
    refine Q.continuous.continuousAt.eventually_ne ?_
    rw [← Polynomial.coeff_zero_eq_eval_zero, hQ]
    exact one_ne_zero
  obtain ⟨n, hn⟩ := (ht.eventually hP0).exists
  refine ⟨n, ?_⟩
  have hs : RankinSelberg.spectralPoint q (n : ℂ) = ((q : ℂ)⁻¹) ^ n := by
    rw [RankinSelberg.spectralPoint, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
  rw [hs]
  exact hn

/-- The unramified pair Euler polynomial `∏_(i,j) (1 - a_i b_j X)` has constant term `1`. -/
theorem pairEulerPolynomial_coeff_zero {n m : ℕ} (a : Unramified.Eigenvalues n)
    (b : Unramified.Eigenvalues m) : (pairEulerPolynomial a b).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, pairEulerPolynomial, Polynomial.eval_multiset_prod,
    Multiset.map_map]
  have e : ((Polynomial.eval (0 : ℂ)) ∘ fun z : ℂˣ × ℂˣ => 1 - C ((z.1 : ℂ) * z.2) * X) =
      fun _ => (1 : ℂ) := by
    funext z
    simp
  rw [e, Multiset.map_const', Multiset.prod_replicate, one_pow]

/-! ### The local factors outside `S` -/

section Local

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
  {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)

/-- The denominator `s ↦ P_v(q_v^(-s))` of an unramified pair factor is entire. -/
theorem differentiable_partialEulerDenominator (v : {v : FinitePlace F // v ∉ S}) :
    Differentiable ℂ (fun s =>
      (pairEulerPolynomial (P.spectralSystem.eigenvalues v.1 fun h => v.2 (hP h))
        (P'.spectralSystem.eigenvalues v.1 fun h => v.2 (hP' h))).eval
        (RankinSelberg.spectralPoint (residueCardinality v.1) s)) :=
  differentiable_eval_spectralPoint _
    (zero_lt_one.trans (FinitePairFactorChoice.one_lt_residueCardinality v.1))

/-- Each unramified pair factor `L(s, Π_v × Π'_v)` is meromorphic on `ℂ`. -/
theorem meromorphic_partialEulerFactor (v : {v : FinitePlace F // v ∉ S}) :
    Meromorphic (partialEulerFactor P P' hP hP' v) := fun z =>
  ((differentiable_partialEulerDenominator P P' hP hP' v).analyticAt z).meromorphicAt.inv

/-- Each unramified pair factor `L(s, Π_v × Π'_v)` has nonpositive order at every point:
it is the reciprocal of an entire function that does not vanish identically. -/
theorem meromorphicOrderAt_partialEulerFactor_nonpos (v : {v : FinitePlace F // v ∉ S})
    (x : ℂ) : meromorphicOrderAt (partialEulerFactor P P' hP hP' v) x ≤ 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_eval_spectralPoint_ne_zero (pairEulerPolynomial_coeff_zero _ _)
    (FinitePairFactorChoice.one_lt_residueCardinality v.1)
  exact meromorphicOrderAt_inv_nonpos (differentiable_partialEulerDenominator P P' hP hP' v)
    hz₀ x

end Local

/-! ### Uniqueness of the partial L-function -/

section Uniqueness

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {S : Finset (FinitePlace F)} {hP : P.exceptional ⊆ S} {hP' : P'.exceptional ⊆ S}

/-- A partial L-function is meromorphic on `ℂ`, in the form `∀ z, MeromorphicAt L z`. -/
theorem IsPartialPairLFunction.meromorphic {L : ℂ → ℂ}
    (hL : IsPartialPairLFunction P P' hP hP' L) : Meromorphic L := fun z =>
  hL.1 z (Set.mem_univ z)

/-- **Uniqueness.** Two partial L-functions for the same data agree in a punctured
neighbourhood of every point: they agree on a right half-plane, where both are the value of
the same Euler product, and then everywhere off a discrete set by the identity theorem. -/
theorem IsPartialPairLFunction.meromorphicEq {L L' : ℂ → ℂ}
    (hL : IsPartialPairLFunction P P' hP hP' L)
    (hL' : IsPartialPairLFunction P P' hP hP' L') :
    FunctionalEquationComparison.MeromorphicEq L L' := by
  obtain ⟨σ, hσ⟩ := hL.2
  obtain ⟨σ', hσ'⟩ := hL'.2
  refine FunctionalEquationComparison.eq_on_halfplane_meromorphicEq (σ := max σ σ')
    hL.meromorphic hL'.meromorphic fun s hs => ?_
  exact (hσ s (lt_of_le_of_lt (le_max_left _ _) hs)).2.unique
    (hσ' s (lt_of_le_of_lt (le_max_right _ _) hs)).2

/-- **Uniqueness of orders.** Two partial L-functions for the same data have the same
`meromorphicOrderAt` at every point. -/
theorem IsPartialPairLFunction.meromorphicOrderAt_eq {L L' : ℂ → ℂ}
    (hL : IsPartialPairLFunction P P' hP hP' L)
    (hL' : IsPartialPairLFunction P P' hP hP' L') (z : ℂ) :
    meromorphicOrderAt L z = meromorphicOrderAt L' z :=
  meromorphicOrderAt_congr (hL.meromorphicEq hL' z)

end Uniqueness

/-! ### Enlarging the set of places -/

section Enlargement

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {S S₀ : Finset (FinitePlace F)}

/-- The places outside `S` that are not in `S₀`, as the places outside `S₀`, for `S ⊆ S₀`. -/
def enlargementEquiv [DecidableEq (FinitePlace F)] (hS : S ⊆ S₀) :
    {w : {v : FinitePlace F // v ∉ S} // w ∉ S₀.subtype (fun v => v ∉ S)} ≃
      {v : FinitePlace F // v ∉ S₀} where
  toFun w := ⟨w.1.1, by
    intro h
    apply w.2
    rw [Finset.mem_subtype]
    exact h⟩
  invFun v := ⟨⟨v.1, fun h => v.2 (hS h)⟩, by
    rw [Finset.mem_subtype]
    exact v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Enlargement of `S`.** If `S ⊆ S₀` and `L₀` is a partial L-function outside `S₀`, then
`L₀ · ∏_(v ∈ S₀ \ S) L(s, Π_v × Π'_v)` is a partial L-function outside `S`. -/
theorem isPartialPairLFunction_of_superset [DecidableEq (FinitePlace F)]
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (hS : S ⊆ S₀) {L₀ : ℂ → ℂ}
    (hL₀ : IsPartialPairLFunction P P' (hP.trans hS) (hP'.trans hS) L₀) :
    IsPartialPairLFunction P P' hP hP' (fun s =>
      L₀ s * ∏ w ∈ S₀.subtype (fun v => v ∉ S), partialEulerFactor P P' hP hP' w s) := by
  obtain ⟨σ, hσ⟩ := hL₀.2
  refine ⟨fun z _ => (hL₀.meromorphic z).mul
    (MeromorphicAt.fun_prod (F := fun w s => partialEulerFactor P P' hP hP' w s)
      (fun w _ => meromorphic_partialEulerFactor P P' hP hP' w z)), σ, fun s hs => ?_⟩
  obtain ⟨hsum, hprod⟩ := hσ s hs
  set E : Finset {v : FinitePlace F // v ∉ S} := S₀.subtype (fun v => v ∉ S)
  have hfac : ∀ w : {w : {v : FinitePlace F // v ∉ S} // w ∉ E},
      partialEulerFactor P P' hP hP' w.1 s =
        partialEulerFactor P P' (hP.trans hS) (hP'.trans hS) (enlargementEquiv hS w) s :=
    fun _ => rfl
  constructor
  · refine (E.summable_compl_iff (f := fun w => ‖partialEulerFactor P P' hP hP' w s - 1‖)).mp ?_
    have h := (enlargementEquiv hS).summable_iff.mpr hsum
    refine h.congr fun w => ?_
    simp only [Function.comp_apply, hfac]
  · have h := (enlargementEquiv hS).hasProd_iff.mpr hprod
    have e : ((fun v => partialEulerFactor P P' (hP.trans hS) (hP'.trans hS) v s) ∘
        enlargementEquiv hS) = fun w => partialEulerFactor P P' hP hP' w.1 s :=
      funext fun w => (hfac w).symm
    rw [e] at h
    have h' : HasProd ((fun w => partialEulerFactor P P' hP hP' w s) ∘ (↑) :
        ((E : Set {v : FinitePlace F // v ∉ S})ᶜ : Set _) → ℂ) (L₀ s) := h
    exact h'.compl_mul (E.hasProd fun w => partialEulerFactor P P' hP hP' w s)

/-- **Existence passes to smaller sets.** A partial L-function outside `S₀ ⊇ S` gives one
outside `S`. -/
theorem exists_isPartialPairLFunction_of_superset (hP : P.exceptional ⊆ S)
    (hP' : P'.exceptional ⊆ S) (hS : S ⊆ S₀)
    (h : ∃ L₀ : ℂ → ℂ, IsPartialPairLFunction P P' (hP.trans hS) (hP'.trans hS) L₀) :
    ∃ L : ℂ → ℂ, IsPartialPairLFunction P P' hP hP' L := by
  classical
  obtain ⟨L₀, hL₀⟩ := h
  exact ⟨_, isPartialPairLFunction_of_superset hP hP' hS hL₀⟩

/-- **Nonpositive orders pass to smaller sets.** If `S ⊆ S₀`, then at every point where a
partial L-function outside `S₀` has nonpositive order, every partial L-function outside
`S` has nonpositive order. -/
theorem meromorphicOrderAt_nonpos_of_superset (hP : P.exceptional ⊆ S)
    (hP' : P'.exceptional ⊆ S) (hS : S ⊆ S₀) {L₀ : ℂ → ℂ}
    (hL₀ : IsPartialPairLFunction P P' (hP.trans hS) (hP'.trans hS) L₀) {L : ℂ → ℂ}
    (hL : IsPartialPairLFunction P P' hP hP' L) {z : ℂ}
    (hz : meromorphicOrderAt L₀ z ≤ 0) : meromorphicOrderAt L z ≤ 0 := by
  classical
  have hL₁ := isPartialPairLFunction_of_superset hP hP' hS hL₀
  rw [hL.meromorphicOrderAt_eq hL₁ z]
  have hprod : MeromorphicAt (fun s => ∏ w ∈ S₀.subtype (fun v => v ∉ S),
      partialEulerFactor P P' hP hP' w s) z :=
    MeromorphicAt.fun_prod (F := fun w s => partialEulerFactor P P' hP hP' w s)
      (fun w _ => meromorphic_partialEulerFactor P P' hP hP' w z)
  have e : (fun s => L₀ s * ∏ w ∈ S₀.subtype (fun v => v ∉ S),
      partialEulerFactor P P' hP hP' w s) =
      L₀ * fun s => ∏ w ∈ S₀.subtype (fun v => v ∉ S), partialEulerFactor P P' hP hP' w s := rfl
  rw [e, meromorphicOrderAt_mul (hL₀.meromorphic z) hprod,
    meromorphicOrderAt_fun_prod (f := fun w s => partialEulerFactor P P' hP hP' w s)
      (fun w _ => meromorphic_partialEulerFactor P P' hP hP' w z)]
  exact add_nonpos hz (Finset.sum_nonpos fun w _ =>
    meromorphicOrderAt_partialEulerFactor_nonpos P P' hP hP' w z)

end Enlargement

end CuspidalPairBoundaryNonvanishing

open CuspidalPairBoundaryNonvanishing

/-- **Shahidi's theorem for an enlarged set of places.** For every finite set `S` of finite
places containing both exceptional sets there are a finite set `S₀ ⊇ S` and a partial
L-function `L^(S₀)(s, Π × Π')` with nonpositive order at every point `1 + iy`, `y` real. -/
def CuspidalPairBoundaryNonvanishingEnlargedStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S),
    ∃ (S₀ : Finset (FinitePlace F)) (hS : S ⊆ S₀) (L₀ : ℂ → ℂ),
      IsPartialPairLFunction P P' (hP.trans hS) (hP'.trans hS) L₀ ∧
        ∀ y : ℝ, meromorphicOrderAt L₀ (1 + y * Complex.I) ≤ 0

/-- The reduction: Shahidi's theorem for enlarged sets of places implies
`CuspidalPairBoundaryNonvanishingStatement`, at the same universes. -/
def CuspidalPairBoundaryNonvanishingReductionStatement : Prop :=
  CuspidalPairBoundaryNonvanishingEnlargedStatement.{u, uQ} →
    CuspidalPairBoundaryNonvanishingStatement.{u, uQ}

/-- **The reduction `CuspidalPairBoundaryNonvanishingReductionStatement`.** -/
theorem cuspidalPairBoundaryNonvanishingReduction :
    CuspidalPairBoundaryNonvanishingReductionStatement.{u, uQ} := by
  intro h F _ _ _ r t T T' hT hT' P P' S hP hP'
  obtain ⟨S₀, hS, L₀, hL₀, hord⟩ := h F r t T T' hT hT' P P' S hP hP'
  exact ⟨exists_isPartialPairLFunction_of_superset hP hP' hS ⟨L₀, hL₀⟩,
    fun L hL y => meromorphicOrderAt_nonpos_of_superset hP hP' hS hL₀ hL (hord y)⟩

end Langlands.Global
