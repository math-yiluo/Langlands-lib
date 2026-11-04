import Langlands.GroupScheme.FlagCoreLimit
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group

/-! # Linear algebra of the flag covering core -/

namespace Langlands.GroupScheme.FlagCore

open MvPolynomial Matrix
open scoped Kronecker

variable {k : Type*} [Field k]

section Polynomial

variable {σ : Type*} [Fintype σ]

/-- The substitution `X i ↦ ∑ l, M i l X l`, so that evaluating the result at `x` is evaluating
the original polynomial at `M *ᵥ x`. -/
noncomputable def linearSubst (M : Matrix σ σ k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  bind₁ fun i => ∑ l, C (M i l) * X l

theorem eval_linearSubst (M : Matrix σ σ k) (f : MvPolynomial σ k) (x : σ → k) :
    eval x (linearSubst M f) = eval (M *ᵥ x) f := by
  change eval₂Hom (RingHom.id k) x (bind₁ _ f) = _
  rw [eval₂Hom_bind₁]
  change eval (fun i => eval x (∑ l, C (M i l) * X l)) f = _
  rw [show (fun i => eval x (∑ l, C (M i l) * X l)) = M *ᵥ x from
    funext fun i => by simp [mulVec, dotProduct]]

theorem isHomogeneous_linearSubst (M : Matrix σ σ k) {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) : (linearSubst M f).IsHomogeneous d := by
  have h := hf.aeval (n := 1) (fun i => ∑ l, C (M i l) * X l)
    (fun i => IsHomogeneous.sum _ _ _ fun l _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h

end Polynomial

section Orbit

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {Γ : Type*}

/-- A family of vectors has a closed projective orbit in the sense of rational points: every
nonzero vector satisfying all homogeneous equations of the family is a nonzero multiple of one
of its members. -/
def IsClosedOrbit (o : Γ → σ → k) : Prop :=
  ∀ c : σ → k, c ≠ 0 →
    (∀ (f : MvPolynomial σ k) (d : ℕ), f.IsHomogeneous d → (∀ g, eval (o g) f = 0) →
      eval c f = 0) →
    ∃ g, ∃ a : k, a ≠ 0 ∧ c = a • o g

/-- Closed orbits are preserved by an invertible linear change of coordinates. -/
theorem IsClosedOrbit.mulVec [DecidableEq σ] {o : Γ → σ → k} (ho : IsClosedOrbit o) (A A' : Matrix σ σ k)
    (hA : A' * A = 1) (hA' : A * A' = 1) : IsClosedOrbit fun g => A *ᵥ o g := by
  intro c hc hfc
  obtain ⟨g, a, ha, hg⟩ := ho (A' *ᵥ c) (by
    intro h0
    apply hc
    have := congrArg (A *ᵥ ·) h0
    simpa [mulVec_mulVec, hA'] using this) (by
    intro f d hf hfo
    rw [← eval_linearSubst]
    apply hfc _ d (isHomogeneous_linearSubst A' hf)
    intro g
    rw [eval_linearSubst, mulVec_mulVec, hA, one_mulVec]
    exact hfo g)
  refine ⟨g, a, ha, ?_⟩
  have := congrArg (A *ᵥ ·) hg
  simpa [mulVec_mulVec, hA', mulVec_smul] using this

/-- Closed orbits are preserved by rescaling each member by a nonzero scalar. -/
theorem IsClosedOrbit.smul {o : Γ → σ → k} (ho : IsClosedOrbit o) (s : Γ → k)
    (hs : ∀ g, s g ≠ 0) : IsClosedOrbit fun g => s g • o g := by
  intro c hc hfc
  obtain ⟨g, a, ha, hg⟩ := ho c hc (by
    intro f d hf hfo
    apply hfc f d hf
    intro g
    rw [eval_smul_of_isHomogeneous hf, hfo g, mul_zero])
  refine ⟨g, a / s g, div_ne_zero ha (hs g), ?_⟩
  rw [hg, smul_smul, div_mul_cancel₀ _ (hs g)]

omit [Fintype σ] [Fintype τ] in
/-- Closed orbits are preserved by reindexing the coordinates. -/
theorem IsClosedOrbit.reindex {o : Γ → σ → k} (ho : IsClosedOrbit o) (e : τ ≃ σ) :
    IsClosedOrbit fun g => o g ∘ e := by
  intro c hc hfc
  obtain ⟨g, a, ha, hg⟩ := ho (c ∘ e.symm) (by
    intro h0
    apply hc
    funext t
    simpa using congrFun h0 (e t)) (by
    intro f d hf hfo
    have h := hfc (rename e.symm f) d (hf.rename_isHomogeneous) (by
      intro g
      rw [eval_rename, show (o g ∘ e) ∘ e.symm = o g from funext fun x => by simp]
      exact hfo g)
    rwa [eval_rename] at h)
  refine ⟨g, a, ha, ?_⟩
  funext t
  simpa using congrFun hg (e t)

/-- The contraction step.  If the vectors `M *ᵥ (z ^ dd i * u i)_i`, `z ≠ 0`, are multiples
of orbit members, then so is `M *ᵥ` the lowest-weight part of `u`. -/
theorem IsClosedOrbit.exists_weightPart [Infinite k] [DecidableEq σ] {o : Γ → σ → k} (ho : IsClosedOrbit o)
    (M M' : Matrix σ σ k) (hM : M' * M = 1) (dd : σ → ℤ) (u : σ → k) (c : ℤ)
    (hc : ∀ i, u i ≠ 0 → c ≤ dd i) (hne : ∃ i, u i ≠ 0 ∧ dd i = c)
    (hcurve : ∀ z : k, z ≠ 0 → ∃ g, ∃ a : k, M *ᵥ (fun i => z ^ dd i * u i) = a • o g) :
    ∃ g, ∃ a : k, a ≠ 0 ∧ M *ᵥ weightPart dd u c = a • o g := by
  apply ho
  · intro h0
    obtain ⟨i, hi, hdi⟩ := hne
    have h1 : weightPart dd u c = 0 := by
      have := congrArg (M' *ᵥ ·) h0
      simpa [mulVec_mulVec, hM] using this
    have h2 := congrFun h1 i
    simp only [weightPart, GeneralLinear.weightPart, hdi, ite_true, Pi.zero_apply] at h2
    exact hi h2
  · intro f m hf hfo
    rw [← eval_linearSubst]
    apply eval_weightPart_eq_zero (isHomogeneous_linearSubst M hf) dd u c hc
    intro z hz
    obtain ⟨g, a, hg⟩ := hcurve z hz
    rw [eval_linearSubst, hg, eval_smul_of_isHomogeneous hf, hfo g, mul_zero]

end Orbit

section Weights

variable {ι : Type*} [Fintype ι] {I : Type*} [Fintype I]

private theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {α : Type*} (s : Finset α)
    (f : α → ℤ) (a : G) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]

/-- Finitely many integral weight vectors are separated by a single integral cocharacter. -/
theorem exists_separating (wt : ι → I → ℤ) :
    ∃ ν : I → ℤ, ∀ i l, ∑ a, ν a * wt i a = ∑ a, ν a * wt l a → wt i = wt l := by
  classical
  let F : MvPolynomial I ℤ := ∏ p : ι × ι,
    if wt p.1 = wt p.2 then 1 else ∑ a, C (wt p.1 a - wt p.2 a) * X a
  have hF : F ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p _
    split_ifs with h
    · exact one_ne_zero
    · obtain ⟨a₀, ha₀⟩ : ∃ a, wt p.1 a ≠ wt p.2 a := by
        by_contra hne
        push Not at hne
        exact h (funext hne)
      intro h0
      have := congrArg (eval (Pi.single a₀ 1)) h0
      simp [Pi.single_apply] at this
      omega
  obtain ⟨x, hx⟩ : ∃ x, eval x F ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hF (MvPolynomial.funext fun x => by simpa using hall x)
  refine ⟨x, fun i l h => ?_⟩
  by_contra hne
  have hx' : ∏ p : ι × ι, eval x
      (if wt p.1 = wt p.2 then 1 else ∑ a, C (wt p.1 a - wt p.2 a) * X a) ≠ 0 := by
    simpa [F, map_prod] using hx
  have hfac := (Finset.prod_ne_zero_iff.mp hx') (i, l) (Finset.mem_univ _)
  simp only [hne, ite_false, map_sum, map_mul, eval_C, eval_X] at hfac
  apply hfac
  have : ∑ a, (wt i a - wt l a) * x a = ∑ a, x a * wt i a - ∑ a, x a * wt l a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, h, sub_self]

/-- In an infinite field, two integers inducing the same power map on units are equal. -/
theorem eq_of_forall_zpow_eq [Infinite k] {m m' : ℤ} (h : ∀ z : kˣ, z ^ m = z ^ m') :
    m = m' := by
  by_contra hne
  set N := (m - m').natAbs with hNdef
  have hN : 0 < N := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hroot : ∀ z : k, z ≠ 0 → (Polynomial.X ^ N - Polynomial.C 1 : Polynomial k).IsRoot z := by
    intro z hz
    have h1 : (Units.mk0 z hz) ^ (m - m') = 1 := by rw [zpow_sub, h, mul_inv_cancel]
    have h2 : (Units.mk0 z hz) ^ N = 1 := by
      rcases Int.natAbs_eq (m - m') with h3 | h3
      · rw [h3] at h1
        exact_mod_cast h1
      · rw [h3, zpow_neg, inv_eq_one] at h1
        exact_mod_cast h1
    have h4 := congrArg Units.val h2
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h4
    simp [Polynomial.IsRoot, h4]
  have hzero : (Polynomial.X ^ N - Polynomial.C 1 : Polynomial k) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := ({0} : Set k)ᶜ)
    · intro z hz
      exact hroot z hz
    · exact (Set.finite_singleton 0).infinite_compl
  exact Polynomial.X_pow_sub_C_ne_zero hN 1 hzero

/-- A nonzero vector has a lowest weight among its nonzero coordinates. -/
theorem exists_min_level (d : ι → ℤ) (u : ι → k) (hu : u ≠ 0) :
    ∃ c : ℤ, (∀ i, u i ≠ 0 → c ≤ d i) ∧ ∃ i, u i ≠ 0 ∧ d i = c := by
  classical
  have hne : (Finset.univ.filter fun i => u i ≠ 0).Nonempty := by
    by_contra h
    apply hu
    funext i
    by_contra hi
    exact h (Finset.filter_nonempty_iff.mpr ⟨i, Finset.mem_univ _, hi⟩)
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ d hne
  refine ⟨d i₀, fun i hi => hmin i (by simp [hi]), i₀, by simpa using hi₀, rfl⟩

omit [Fintype ι] in
theorem weightPart_ne_zero_level {d : ι → ℤ} {u : ι → k} {c : ℤ} {i : ι}
    (h : weightPart d u c i ≠ 0) : d i = c := by
  by_contra hne
  exact h (by simp [weightPart, GeneralLinear.weightPart, hne])

theorem exists_of_dotProduct_weightPart_ne_zero {d : ι → ℤ} {x y : ι → k} {c : ℤ}
    (h : x ⬝ᵥ weightPart d y c ≠ 0) : ∃ i, x i ≠ 0 ∧ d i = c ∧ y i ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  apply Finset.sum_eq_zero
  intro i _
  by_cases hx : x i = 0
  · simp [hx]
  · by_cases hdi : d i = c
    · simp [weightPart, GeneralLinear.weightPart, hdi, hall i hx hdi]
    · simp [weightPart, GeneralLinear.weightPart, hdi]

theorem dotProduct_weightPart_of_level {d : ι → ℤ} {x y : ι → k} {c : ℤ}
    (hx : ∀ i, x i ≠ 0 → d i = c) : x ⬝ᵥ weightPart d y c = x ⬝ᵥ y := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = 0
  · simp [h]
  · simp [weightPart, GeneralLinear.weightPart, hx i h]

theorem weightPart_dotProduct_weightPart (d : ι → ℤ) (x y : ι → k) (c : ℤ) :
    weightPart d x c ⬝ᵥ weightPart d y c = x ⬝ᵥ weightPart d y c := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : d i = c <;> simp [weightPart, GeneralLinear.weightPart, h]

omit [Fintype I] in
/-- Equal cocharacter levels inside one support give one weight vector. -/
theorem exists_weight_of_level {wt : ι → I → ℤ} {d : ι → ℤ}
    (hsep : ∀ i l, d i = d l → wt i = wt l) (u : ι → k) (c : ℤ)
    (hu : ∀ i, u i ≠ 0 → d i = c) : ∃ μ : I → ℤ, ∀ i, u i ≠ 0 → wt i = μ := by
  by_cases h : ∃ i₀, u i₀ ≠ 0
  · obtain ⟨i₀, hi₀⟩ := h
    exact ⟨wt i₀, fun i hi => hsep i i₀ ((hu i hi).trans (hu i₀ hi₀).symm)⟩
  · push Not at h
    exact ⟨0, fun i hi => absurd (h i) hi⟩

variable [DecidableEq ι]

/-- The torus character values on a diagonal coordinate. -/
abbrev charValue (wt : ι → I → ℤ) (s : I → kˣ) (i : ι) : kˣ := ∏ a, s a ^ wt i a

theorem diagonal_mulVec_of_weight (wt : ι → I → ℤ) (s : I → kˣ) (μ : I → ℤ) (u : ι → k)
    (hu : ∀ i, u i ≠ 0 → wt i = μ) :
    diagonal (fun i => (charValue wt s i : k)) *ᵥ u = ((∏ a, s a ^ μ a : kˣ) : k) • u := by
  funext i
  rw [mulVec_diagonal]
  by_cases h : u i = 0
  · simp [h]
  · simp only [charValue, hu i h, Pi.smul_apply, smul_eq_mul]

theorem vecMul_diagonal_of_weight (wt : ι → I → ℤ) (s : I → kˣ) (μ : I → ℤ) (u : ι → k)
    (hu : ∀ i, u i ≠ 0 → wt i = μ) :
    u ᵥ* diagonal (fun i => (charValue wt s i : k)) = ((∏ a, s a ^ μ a : kˣ) : k) • u := by
  funext i
  rw [vecMul_diagonal]
  by_cases h : u i = 0
  · simp [h]
  · simp only [charValue, hu i h, Pi.smul_apply, smul_eq_mul, mul_comm]

end Weights

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kronecker_one_mulVec_tmul (A : Matrix ι ι k) (x y : ι → k) :
    (A ⊗ₖ (1 : Matrix ι ι k)) *ᵥ (fun p : ι × ι => x p.1 * y p.2) =
      fun p => (A *ᵥ x) p.1 * y p.2 := by
  funext p
  change ∑ q : ι × ι, (A ⊗ₖ (1 : Matrix ι ι k)) p q * (x q.1 * y q.2) =
    (∑ i, A p.1 i * x i) * y p.2
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [kronecker_apply, one_apply_eq]
    ring
  · intro l _ hl
    rw [kronecker_apply, one_apply_ne (Ne.symm hl)]
    ring
  · simp

omit [Fintype ι] [DecidableEq ι] in
/-- Two equal nonzero pure tensors have proportional factors. -/
theorem exists_smul_of_tmul_eq {x y x₂ y₂ : ι → k} {a : k} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (fun p : ι × ι => x p.1 * y p.2) = a • fun p : ι × ι => x₂ p.1 * y₂ p.2) :
    (∃ b : k, x₂ = b • x) ∧ ∃ b : k, y₂ = b • y := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (funext hall)
  obtain ⟨l₀, hl₀⟩ : ∃ l, y l ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hy (funext hall)
  have h00 := congrFun h (i₀, l₀)
  simp only [Pi.smul_apply, smul_eq_mul] at h00
  have hne : a * (x₂ i₀ * y₂ l₀) ≠ 0 := by
    rw [← h00]
    exact mul_ne_zero hi₀ hl₀
  have ha : a ≠ 0 := left_ne_zero_of_mul hne
  have hx₂ : x₂ i₀ ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have hy₂ : y₂ l₀ ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hne)
  constructor
  · refine ⟨y l₀ / (a * y₂ l₀), funext fun i => ?_⟩
    have hi := congrFun h (i, l₀)
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    field_simp
    linear_combination -hi
  · refine ⟨x i₀ / (a * x₂ i₀), funext fun l => ?_⟩
    have hl := congrFun h (i₀, l)
    simp only [Pi.smul_apply, smul_eq_mul] at hl ⊢
    field_simp
    linear_combination -hl

end Tensor

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {I : Type*} [Fintype I]
  {Γ : Type*} [Group Γ]

/-- A vector spans a line stable under all torus points `τ s`. -/
def IsTorusFixed (ρ : Γ →* GL ι k) (τ : (I → kˣ) → Γ) (u : ι → k) : Prop :=
  ∀ s, ∃ c : k, (ρ (τ s) : Matrix ι ι k) *ᵥ u = c • u

omit [Fintype I] in
theorem IsTorusFixed.smul {ρ : Γ →* GL ι k} {τ : (I → kˣ) → Γ} {u : ι → k}
    (h : IsTorusFixed ρ τ u) (a : k) : IsTorusFixed ρ τ (a • u) := by
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨c, by rw [mulVec_smul, hc, smul_comm]⟩

omit [Group Γ] in
theorem exists_dotProduct_ne_zero (o : Γ → ι → k)
    (hspan : Submodule.span k (Set.range o) = ⊤) {r : ι → k} (hr : r ≠ 0) :
    ∃ g, r ⬝ᵥ o g ≠ 0 := by
  by_contra h
  push Not at h
  apply hr
  have hall : ∀ x ∈ Submodule.span k (Set.range o), r ⬝ᵥ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h g
    | zero => exact dotProduct_zero r
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
  funext l
  have := hall (Pi.single l 1) (hspan ▸ Submodule.mem_top)
  simpa [dotProduct_single] using this

theorem mulVec_ne_zero (X : GL ι k) {v : ι → k} (hv : v ≠ 0) : (X : Matrix ι ι k) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg ((↑X⁻¹ : Matrix ι ι k) *ᵥ ·) h
  simp only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at this
  exact this

theorem vecMul_ne_zero (X : GL ι k) {v : ι → k} (hv : v ≠ 0) : v ᵥ* (X : Matrix ι ι k) ≠ 0 := by
  intro h
  apply hv
  have := congrArg (· ᵥ* (↑X⁻¹ : Matrix ι ι k)) h
  simp only [vecMul_vecMul, Units.mul_inv, vecMul_one, zero_vecMul] at this
  exact this

theorem conj_mulVec (P : GL ι k) (D : Matrix ι ι k) (u : ι → k) :
    ((P : Matrix ι ι k) * D * (↑P⁻¹ : Matrix ι ι k)) *ᵥ ((P : Matrix ι ι k) *ᵥ u) =
      (P : Matrix ι ι k) *ᵥ (D *ᵥ u) := by
  simp only [mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem vecMul_conj (P : GL ι k) (D : Matrix ι ι k) (u : ι → k) :
    (u ᵥ* (↑P⁻¹ : Matrix ι ι k)) ᵥ* ((P : Matrix ι ι k) * D * (↑P⁻¹ : Matrix ι ι k)) =
      (u ᵥ* D) ᵥ* (↑P⁻¹ : Matrix ι ι k) := by
  simp only [vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- If `w X = κ w` then `w X⁻¹ = κ⁻¹ w`. -/
theorem vecMul_inv_of_vecMul_eq (X : GL ι k) (w : ι → k) (κ : kˣ)
    (h : w ᵥ* (X : Matrix ι ι k) = (κ : k) • w) :
    w ᵥ* (↑X⁻¹ : Matrix ι ι k) = ((κ⁻¹ : kˣ) : k) • w := by
  calc w ᵥ* (↑X⁻¹ : Matrix ι ι k)
      = ((κ⁻¹ : kˣ) : k) • (((κ : k) • w) ᵥ* (↑X⁻¹ : Matrix ι ι k)) := by
        rw [smul_vecMul, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = ((κ⁻¹ : kˣ) : k) • w := by
        rw [← h, vecMul_vecMul, Units.mul_inv, vecMul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- The character values on the points of the cocharacter `z ↦ (z ^ ν a)_a`. -/
theorem charValue_cochar (wt : ι → I → ℤ) {ν : I → ℤ} {d : ι → ℤ}
    (hd : ∀ i, d i = ∑ a, ν a * wt i a) (z : kˣ) (i : ι) :
    charValue wt (fun a => z ^ ν a) i = z ^ d i := by
  simp only [charValue, ← zpow_mul, hd]
  exact prod_zpow_eq_zpow_sum _ _ _

/-- The orbit vector `ρ(g) e`. -/
def orbitVec (ρ : Γ →* GL ι k) (e : ι → k) (g : Γ) : ι → k := (ρ g : Matrix ι ι k) *ᵥ e

/-- The dual orbit vector `w₀ ρ(g)⁻¹`, the transform of the linear form `w₀` by `g`. -/
def dualOrbitVec (ρ : Γ →* GL ι k) (w₀ : ι → k) (g : Γ) : ι → k :=
  w₀ ᵥ* (ρ g⁻¹ : Matrix ι ι k)

/-- The coordinates `(ρ(g) e)_i (w₀ ρ(g)⁻¹)_l` of the pure tensor of the two orbit vectors. -/
def tensorOrbitVec (ρ : Γ →* GL ι k) (e w₀ : ι → k) (g : Γ) : ι × ι → k :=
  fun p => orbitVec ρ e g p.1 * dualOrbitVec ρ w₀ g p.2

section OrbitVec

variable (ρ : Γ →* GL ι k)

theorem orbitVec_mul (e : ι → k) (x g : Γ) :
    orbitVec ρ e (x * g) = (ρ x : Matrix ι ι k) *ᵥ orbitVec ρ e g := by
  simp only [orbitVec, map_mul, Units.val_mul, mulVec_mulVec]

theorem dualOrbitVec_mul (w₀ : ι → k) (x g : Γ) :
    dualOrbitVec ρ w₀ (x * g) = dualOrbitVec ρ w₀ g ᵥ* (ρ x⁻¹ : Matrix ι ι k) := by
  simp only [dualOrbitVec, _root_.mul_inv_rev, map_mul, Units.val_mul, vecMul_vecMul]

theorem orbitVec_ne_zero {e : ι → k} (he : e ≠ 0) (g : Γ) : orbitVec ρ e g ≠ 0 :=
  mulVec_ne_zero (ρ g) he

theorem dualOrbitVec_ne_zero {w₀ : ι → k} (hw₀ : w₀ ≠ 0) (g : Γ) : dualOrbitVec ρ w₀ g ≠ 0 :=
  vecMul_ne_zero (ρ g⁻¹) hw₀

theorem dualOrbitVec_dotProduct_orbitVec (e w₀ : ι → k) (g h : Γ) :
    dualOrbitVec ρ w₀ g ⬝ᵥ orbitVec ρ e h = w₀ ⬝ᵥ orbitVec ρ e (g⁻¹ * h) := by
  simp only [dualOrbitVec, orbitVec, ← dotProduct_mulVec, mulVec_mulVec, map_mul,
    Units.val_mul]

/-- If the stabilizer of the line of `e` stabilizes the line of the linear form `w₀`, then
the stabilizer of the line of `ρ(g) e` stabilizes the line of `w₀ ρ(g)⁻¹`. -/
theorem dualOrbitVec_eigen {e w₀ : ι → k}
    (hstab : ∀ h : Γ, (∃ c : k, orbitVec ρ e h = c • e) →
      ∃ c : k, w₀ ᵥ* (ρ h : Matrix ι ι k) = c • w₀)
    {g x : Γ} {c : k} (hx : (ρ x : Matrix ι ι k) *ᵥ orbitVec ρ e g = c • orbitVec ρ e g) :
    ∃ c' : k, dualOrbitVec ρ w₀ g ᵥ* (ρ x : Matrix ι ι k) = c' • dualOrbitVec ρ w₀ g := by
  obtain ⟨c', hc'⟩ := hstab (g⁻¹ * x * g) ⟨c, by
    rw [mul_assoc, orbitVec_mul, orbitVec_mul, hx, mulVec_smul, ← orbitVec_mul, inv_mul_cancel]
    simp only [orbitVec, map_one, Units.val_one, one_mulVec]⟩
  refine ⟨c', ?_⟩
  have hcomm : (ρ g⁻¹ : Matrix ι ι k) * (ρ x : Matrix ι ι k) =
      (ρ (g⁻¹ * x * g) : Matrix ι ι k) * (ρ g⁻¹ : Matrix ι ι k) := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_right]
  rw [dualOrbitVec, vecMul_vecMul, hcomm, ← vecMul_vecMul, hc', smul_vecMul]

end OrbitVec

section Torus

variable {ρ : Γ →* GL ι k} {P : GL ι k} {wt : ι → I → ℤ} {τ : (I → kˣ) → Γ}

theorem isTorusFixed_of_level
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {d : ι → ℤ} (hsep : ∀ i l, d i = d l → wt i = wt l) (u : ι → k) (c : ℤ)
    (hu : ∀ i, u i ≠ 0 → d i = c) : IsTorusFixed ρ τ ((P : Matrix ι ι k) *ᵥ u) := by
  obtain ⟨μ, hμ⟩ := exists_weight_of_level hsep u c hu
  intro s
  refine ⟨((∏ a, s a ^ μ a : kˣ) : k), ?_⟩
  rw [hτ, conj_mulVec, diagonal_mulVec_of_weight wt s μ u hμ, mulVec_smul]

theorem vecMul_torus_of_level
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {d : ι → ℤ} (hsep : ∀ i l, d i = d l → wt i = wt l) (u : ι → k) (c : ℤ)
    (hu : ∀ i, u i ≠ 0 → d i = c) (s : I → kˣ) :
    ∃ κ : kˣ, (u ᵥ* (↑P⁻¹ : Matrix ι ι k)) ᵥ* (ρ (τ s) : Matrix ι ι k) =
      (κ : k) • (u ᵥ* (↑P⁻¹ : Matrix ι ι k)) := by
  obtain ⟨μ, hμ⟩ := exists_weight_of_level hsep u c hu
  refine ⟨∏ a, s a ^ μ a, ?_⟩
  rw [hτ, vecMul_conj, vecMul_diagonal_of_weight wt s μ u hμ, smul_vecMul]

theorem torus_curve_mulVec
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {ν : I → ℤ} {d : ι → ℤ} (hd : ∀ i, d i = ∑ a, ν a * wt i a) (z : k) (hz : z ≠ 0)
    (u : ι → k) :
    (ρ (τ fun a => Units.mk0 z hz ^ ν a) : Matrix ι ι k) *ᵥ ((P : Matrix ι ι k) *ᵥ u) =
      (P : Matrix ι ι k) *ᵥ fun i => z ^ d i * u i := by
  rw [hτ, conj_mulVec]
  congr 1
  funext i
  simp only [mulVec_diagonal]
  rw [charValue_cochar wt hd, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem torus_curve_vecMul
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {ν : I → ℤ} {d : ι → ℤ} (hd : ∀ i, d i = ∑ a, ν a * wt i a) (z : k) (hz : z ≠ 0)
    (η : ι → k) :
    η ᵥ* (ρ (τ fun a => Units.mk0 z hz ^ ν a) : Matrix ι ι k) =
      (fun i => z ^ d i * (η ᵥ* (P : Matrix ι ι k)) i) ᵥ* (↑P⁻¹ : Matrix ι ι k) := by
  rw [hτ, ← vecMul_vecMul, ← vecMul_vecMul]
  congr 1
  funext i
  simp only [vecMul_diagonal]
  rw [charValue_cochar wt hd, Units.val_zpow_eq_zpow_val, Units.val_mk0, mul_comm]

omit [Group Γ] in
/-- A linear form which is an eigenvector of all diagonal torus matrices is supported on a
single cocharacter level. -/
theorem level_eq_of_eigen [Infinite k] {ν : I → ℤ} {d : ι → ℤ}
    (hd : ∀ i, d i = ∑ a, ν a * wt i a) {ξ : ι → k}
    (h : ∀ s : I → kˣ, ∃ c : k, ξ ᵥ* diagonal (fun i => (charValue wt s i : k)) = c • ξ)
    {i l : ι} (hi : ξ i ≠ 0) (hl : ξ l ≠ 0) : d i = d l := by
  apply eq_of_forall_zpow_eq (k := k)
  intro z
  obtain ⟨c, hc⟩ := h fun a => z ^ ν a
  have hi' := congrFun hc i
  have hl' := congrFun hc l
  simp only [vecMul_diagonal, Pi.smul_apply, smul_eq_mul] at hi' hl'
  have e1 : (charValue wt (fun a => z ^ ν a) i : k) = c :=
    mul_left_cancel₀ hi (by rw [hi', mul_comm])
  have e2 : (charValue wt (fun a => z ^ ν a) l : k) = c :=
    mul_left_cancel₀ hl (by rw [hl', mul_comm])
  apply Units.ext
  rw [← charValue_cochar wt hd, ← charValue_cochar wt hd, e1, e2]

omit [Fintype I] in
theorem IsTorusFixed.mulVec_of_normalizes {m : Γ} (hm : ∀ s, ∃ s', m⁻¹ * τ s * m = τ s')
    {u : ι → k} (hu : IsTorusFixed ρ τ u) : IsTorusFixed ρ τ ((ρ m : Matrix ι ι k) *ᵥ u) := by
  intro s
  obtain ⟨s', hs'⟩ := hm s
  obtain ⟨c, hc⟩ := hu s'
  refine ⟨c, ?_⟩
  have hcomm : τ s * m = m * τ s' := by
    rw [← hs']
    group
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, hcomm, map_mul, Units.val_mul,
    ← mulVec_mulVec, hc, mulVec_smul]

/-- The contraction step for the orbit of `e` along the cocharacter `z ↦ (z ^ ν a)_a`. -/
theorem exists_orbitVec_weightPart [Infinite k] {e : ι → k} (ho : IsClosedOrbit (orbitVec ρ e))
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {ν : I → ℤ} {d : ι → ℤ} (hd : ∀ i, d i = ∑ a, ν a * wt i a) (g : Γ) (u : ι → k)
    (hu : (P : Matrix ι ι k) *ᵥ u = orbitVec ρ e g) (c : ℤ) (hc : ∀ i, u i ≠ 0 → c ≤ d i)
    (hne : ∃ i, u i ≠ 0 ∧ d i = c) :
    ∃ g₁, ∃ a : k, a ≠ 0 ∧ (P : Matrix ι ι k) *ᵥ weightPart d u c = a • orbitVec ρ e g₁ := by
  apply ho.exists_weightPart (P : Matrix ι ι k) (↑P⁻¹ : Matrix ι ι k) (Units.inv_mul P) d u c hc hne
  intro z hz
  refine ⟨τ (fun a => Units.mk0 z hz ^ ν a) * g, 1, ?_⟩
  rw [one_smul, orbitVec_mul, ← hu, torus_curve_mulVec hτ hd z hz]

theorem isTorusFixed_of_eq_smul
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {d : ι → ℤ} (hsep : ∀ i l, d i = d l → wt i = wt l) {u v : ι → k} {c : ℤ} {a : k}
    (ha : a ≠ 0) (h : (P : Matrix ι ι k) *ᵥ weightPart d u c = a • v) : IsTorusFixed ρ τ v := by
  have h1 := (isTorusFixed_of_level hτ hsep (weightPart d u c) c
    (fun i hi => weightPart_ne_zero_level hi)).smul a⁻¹
  rwa [h, smul_smul, inv_mul_cancel₀ ha, one_smul] at h1

theorem vecMul_diagonal_of_eigen
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    {ξ : ι → k} (s : I → kˣ) {c : k} (h : ξ ᵥ* (ρ (τ s) : Matrix ι ι k) = c • ξ) :
    (ξ ᵥ* (P : Matrix ι ι k)) ᵥ* diagonal (fun i => (charValue wt s i : k)) =
      c • (ξ ᵥ* (P : Matrix ι ι k)) := by
  rw [← smul_vecMul, ← h, vecMul_vecMul, vecMul_vecMul, hτ, Matrix.mul_assoc _ (↑P⁻¹ : Matrix ι ι k),
    Units.inv_mul, Matrix.mul_one]

end Torus

/-- **Linear core of the flag covering argument.**  Let `ρ` be a representation of a group `Γ`
on `k ^ ι`, `k` infinite, and `e ≠ 0` a vector whose orbit spans, whose projective orbit, the
projective orbit of a nonzero linear form `w₀` and the projective orbit of `e ⊗ w₀` are closed,
and such that the stabilizer of the line of `e` stabilizes the line of `w₀`.  Let `τ` be a
family of group elements acting diagonally (in the basis `P`) with integral weights `wt`.
Suppose every element of `U` stabilizes every torus-fixed line of the orbit, and any two
torus-fixed lines of the orbit are related by an element normalizing the torus points.  Then
every orbit line `ρ(g) e` is not annihilated by some linear form `w` which is a
`U`-eigenvector. -/
theorem exists_semiInvariant_form [Infinite k] (ρ : Γ →* GL ι k) {e w₀ : ι → k}
    (he : e ≠ 0) (hw₀ : w₀ ≠ 0)
    (hspan : Submodule.span k (Set.range (orbitVec ρ e)) = ⊤)
    (hstab : ∀ h : Γ, (∃ c : k, orbitVec ρ e h = c • e) →
      ∃ c : k, w₀ ᵥ* (ρ h : Matrix ι ι k) = c • w₀)
    (ho₁ : IsClosedOrbit (orbitVec ρ e)) (ho₂ : IsClosedOrbit (dualOrbitVec ρ w₀))
    (ho₃ : IsClosedOrbit (tensorOrbitVec ρ e w₀))
    (P : GL ι k) (wt : ι → I → ℤ) (τ : (I → kˣ) → Γ)
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) * (↑P⁻¹ : Matrix ι ι k))
    (U : Set Γ)
    (hU : ∀ g, IsTorusFixed ρ τ (orbitVec ρ e g) → ∀ x ∈ U,
      ∃ c : k, (ρ x : Matrix ι ι k) *ᵥ orbitVec ρ e g = c • orbitVec ρ e g)
    (hweyl : ∀ g₁ g₂, IsTorusFixed ρ τ (orbitVec ρ e g₁) → IsTorusFixed ρ τ (orbitVec ρ e g₂) →
      ∃ m : Γ, (∀ s, ∃ s', m⁻¹ * τ s * m = τ s') ∧
        ∃ c : k, orbitVec ρ e (m * g₂) = c • orbitVec ρ e g₁)
    (g : Γ) :
    ∃ w : ι → k, w ⬝ᵥ orbitVec ρ e g ≠ 0 ∧
      ∀ x ∈ U, ∃ c : kˣ, w ᵥ* (ρ x : Matrix ι ι k) = (c : k) • w := by
  classical
  have hPP : (↑P⁻¹ : Matrix ι ι k) * (P : Matrix ι ι k) = 1 := Units.inv_mul P
  have hPP' : (P : Matrix ι ι k) * (↑P⁻¹ : Matrix ι ι k) = 1 := Units.mul_inv P
  have hlift : ∀ h : Γ, ∃ u : ι → k, u ≠ 0 ∧ (P : Matrix ι ι k) *ᵥ u = orbitVec ρ e h := by
    intro h
    refine ⟨(↑P⁻¹ : Matrix ι ι k) *ᵥ orbitVec ρ e h, mulVec_ne_zero P⁻¹ (orbitVec_ne_zero ρ he h),
      ?_⟩
    rw [mulVec_mulVec, hPP', one_mulVec]
  -- (0) A separating cocharacter `ν` with levels `d`.
  obtain ⟨ν, hν⟩ := exists_separating wt
  obtain ⟨d, hd⟩ : ∃ d : ι → ℤ, ∀ i, d i = ∑ a, ν a * wt i a := ⟨_, fun _ => rfl⟩
  have hsep : ∀ i l, d i = d l → wt i = wt l := fun i l h => hν i l (by rw [← hd, ← hd, h])
  -- (1) The lowest-weight limit `ρ(g₁) e` of the line of `ρ(g) e`.
  obtain ⟨v', hv'ne, hv'⟩ := hlift g
  obtain ⟨cm, hcm, hcm'⟩ := exists_min_level d v' hv'ne
  obtain ⟨g₁, a₁, ha₁, hg₁⟩ := exists_orbitVec_weightPart ho₁ hτ hd g v' hv' cm hcm hcm'
  have hfix₁ : IsTorusFixed ρ τ (orbitVec ρ e g₁) := isTorusFixed_of_eq_smul hτ hsep ha₁ hg₁
  -- (2) A torus-fixed line `ρ(g₂) e` of globally lowest weight.
  obtain ⟨i₀, -⟩ : ∃ i, e i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact he (funext hall)
  obtain ⟨im, -, him⟩ := Finset.exists_min_image Finset.univ d ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨gm, hgm⟩ := exists_dotProduct_ne_zero (orbitVec ρ e) hspan
    (vecMul_ne_zero P⁻¹ (Pi.single_ne_zero_iff.2 (one_ne_zero (α := k))) (v := Pi.single im 1))
  obtain ⟨um, -, hum⟩ := hlift gm
  have humi : um im ≠ 0 := by
    rwa [← hum, dotProduct_mulVec, vecMul_vecMul, hPP, vecMul_one, single_dotProduct,
      one_mul] at hgm
  obtain ⟨g₂, a₂, ha₂, hg₂⟩ := exists_orbitVec_weightPart ho₁ hτ hd gm um hum (d im)
    (fun i _ => him i (Finset.mem_univ _)) ⟨im, humi, rfl⟩
  have hfix₂ : IsTorusFixed ρ τ (orbitVec ρ e g₂) := isTorusFixed_of_eq_smul hτ hsep ha₂ hg₂
  -- (3) The Weyl element relating the two torus-fixed lines.
  obtain ⟨m, hm, cw, hcw⟩ := hweyl g₁ g₂ hfix₁ hfix₂
  -- (4) A dual orbit vector not annihilating `ρ(g₂) e`.
  obtain ⟨g₃, hg₃⟩ := exists_dotProduct_ne_zero (orbitVec ρ e) hspan hw₀
  obtain ⟨η', hη'⟩ : ∃ η', dualOrbitVec ρ w₀ (g₂ * g₃⁻¹) ᵥ* (P : Matrix ι ι k) = η' := ⟨_, rfl⟩
  have hη'm : η' ⬝ᵥ weightPart d um (d im) ≠ 0 := by
    have h1 : dualOrbitVec ρ w₀ (g₂ * g₃⁻¹) ⬝ᵥ orbitVec ρ e g₂ ≠ 0 := by
      rwa [dualOrbitVec_dotProduct_orbitVec, show (g₂ * g₃⁻¹)⁻¹ * g₂ = g₃ by group]
    rw [← hη', ← dotProduct_mulVec, hg₂, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero ha₂ h1
  -- (5) Its lowest-weight limit `ξ₀`, a multiple of a dual orbit vector.
  obtain ⟨h₀, a₄, ha₄, hh₀⟩ := ho₂.exists_weightPart (↑P⁻¹ : Matrix ι ι k)ᵀ (P : Matrix ι ι k)ᵀ
    (by rw [← transpose_mul, hPP, transpose_one]) d η' (d im)
    (fun i _ => him i (Finset.mem_univ _))
    (by
      obtain ⟨i, hi, hdi, -⟩ := exists_of_dotProduct_weightPart_ne_zero hη'm
      exact ⟨i, hi, hdi⟩)
    (by
      intro z hz
      refine ⟨(τ fun a => Units.mk0 z hz ^ ν a)⁻¹ * (g₂ * g₃⁻¹), 1, ?_⟩
      rw [one_smul, dualOrbitVec_mul, inv_inv, torus_curve_vecMul hτ hd z hz, mulVec_transpose,
        hη'])
  rw [mulVec_transpose] at hh₀
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀, weightPart d η' (d im) ᵥ* (↑P⁻¹ : Matrix ι ι k) = ξ₀ := ⟨_, rfl⟩
  rw [hξ₀] at hh₀
  have hξ₀m : ξ₀ ⬝ᵥ ((P : Matrix ι ι k) *ᵥ weightPart d um (d im)) ≠ 0 := by
    rwa [← hξ₀, dotProduct_mulVec, vecMul_vecMul, hPP, vecMul_one,
      weightPart_dotProduct_weightPart]
  have hξ₀ne : ξ₀ ≠ 0 := by
    rintro rfl
    exact hξ₀m (zero_dotProduct _)
  have hξ₀eig : ∀ s, ∃ κ : kˣ, ξ₀ ᵥ* (ρ (τ s) : Matrix ι ι k) = (κ : k) • ξ₀ := by
    intro s
    rw [← hξ₀]
    exact vecMul_torus_of_level hτ hsep _ (d im) (fun i hi => weightPart_ne_zero_level hi) s
  -- (6) The tensor contraction: an orbit point `g'` with torus-fixed `ρ(g') e` and
  -- `w₀ ρ(g')⁻¹` proportional to `ξ₀`.
  obtain ⟨u₀, hu₀ne, hu₀⟩ := hlift h₀
  obtain ⟨c₀, hc₀, j₀, hj₀, hdj₀⟩ := exists_min_level d u₀ hu₀ne
  obtain ⟨l₀, hl₀⟩ : ∃ l, ξ₀ l ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hξ₀ne (funext hall)
  obtain ⟨g', a₅, -, hg'⟩ := ho₃.exists_weightPart ((P : Matrix ι ι k) ⊗ₖ (1 : Matrix ι ι k))
    ((↑P⁻¹ : Matrix ι ι k) ⊗ₖ (1 : Matrix ι ι k))
    (by rw [← mul_kronecker_mul, hPP, Matrix.one_mul, one_kronecker_one])
    (fun p => d p.1) (fun p => u₀ p.1 * ξ₀ p.2) c₀
    (fun p hp => hc₀ p.1 (left_ne_zero_of_mul hp)) ⟨(j₀, l₀), mul_ne_zero hj₀ hl₀, hdj₀⟩
    (by
      intro z hz
      obtain ⟨κ, hκ⟩ := hξ₀eig fun a => Units.mk0 z hz ^ ν a
      refine ⟨τ (fun a => Units.mk0 z hz ^ ν a) * h₀, a₄ * κ, ?_⟩
      have hdual : dualOrbitVec ρ w₀ (τ (fun a => Units.mk0 z hz ^ ν a) * h₀) =
          (a₄⁻¹ * ((κ⁻¹ : kˣ) : k)) • ξ₀ := by
        have h1 : dualOrbitVec ρ w₀ h₀ = a₄⁻¹ • ξ₀ := by
          rw [hh₀, smul_smul, inv_mul_cancel₀ ha₄, one_smul]
        rw [dualOrbitVec_mul, h1, smul_vecMul, map_inv, vecMul_inv_of_vecMul_eq _ _ _ hκ,
          smul_smul]
      have horb : orbitVec ρ e (τ (fun a => Units.mk0 z hz ^ ν a) * h₀) =
          (P : Matrix ι ι k) *ᵥ fun i => z ^ d i * u₀ i := by
        rw [orbitVec_mul, ← hu₀, torus_curve_mulVec hτ hd z hz]
      have hfun : (fun p : ι × ι => z ^ d p.1 * (u₀ p.1 * ξ₀ p.2)) =
          fun p => (fun i => z ^ d i * u₀ i) p.1 * ξ₀ p.2 := by
        funext p
        ring
      rw [hfun, kronecker_one_mulVec_tmul (P : Matrix ι ι k) (fun i => z ^ d i * u₀ i) ξ₀]
      funext p
      simp only [tensorOrbitVec, Pi.smul_apply, smul_eq_mul, hdual, horb]
      have hκ1 : (κ : k) * ((κ⁻¹ : kˣ) : k) = 1 := Units.mul_inv κ
      have ha₄1 : a₄ * a₄⁻¹ = 1 := mul_inv_cancel₀ ha₄
      linear_combination (-(((P : Matrix ι ι k) *ᵥ fun i => z ^ d i * u₀ i) p.1 * ξ₀ p.2 *
        ((κ⁻¹ : kˣ) : k) * κ)) * ha₄1 -
        ((P : Matrix ι ι k) *ᵥ fun i => z ^ d i * u₀ i) p.1 * ξ₀ p.2 * hκ1)
  have hwp : weightPart (fun p : ι × ι => d p.1) (fun p => u₀ p.1 * ξ₀ p.2) c₀ =
      fun p => weightPart d u₀ c₀ p.1 * ξ₀ p.2 := by
    funext p
    simp only [weightPart, GeneralLinear.weightPart]
    split_ifs <;> simp
  rw [hwp, kronecker_one_mulVec_tmul] at hg'
  have hwp₀ : weightPart d u₀ c₀ ≠ 0 := by
    intro h0
    have := congrFun h0 j₀
    simp only [weightPart, GeneralLinear.weightPart, hdj₀, ite_true, Pi.zero_apply] at this
    exact hj₀ this
  obtain ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ := exists_smul_of_tmul_eq (mulVec_ne_zero P hwp₀) hξ₀ne
    (x₂ := orbitVec ρ e g') (y₂ := dualOrbitVec ρ w₀ g') hg'
  have hfix' : IsTorusFixed ρ τ (orbitVec ρ e g') := by
    rw [hb]
    exact (isTorusFixed_of_level hτ hsep (weightPart d u₀ c₀) c₀
      (fun i hi => weightPart_ne_zero_level hi)).smul b
  have hb'ne : b' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb'
    exact dualOrbitVec_ne_zero ρ hw₀ g' hb'
  -- (7) The linear form `ξ = w₀ ρ(m g')⁻¹`.
  have hfix : IsTorusFixed ρ τ (orbitVec ρ e (m * g')) := by
    rw [orbitVec_mul]
    exact hfix'.mulVec_of_normalizes hm
  obtain ⟨ξ, hξ⟩ : ∃ ξ, dualOrbitVec ρ w₀ (m * g') = ξ := ⟨_, rfl⟩
  have hξne : ξ ≠ 0 := hξ ▸ dualOrbitVec_ne_zero ρ hw₀ _
  have hξ₁ : ξ ⬝ᵥ ((P : Matrix ι ι k) *ᵥ weightPart d v' cm) ≠ 0 := by
    have h1 : ξ ⬝ᵥ orbitVec ρ e (m * g₂) = dualOrbitVec ρ w₀ g' ⬝ᵥ orbitVec ρ e g₂ := by
      rw [← hξ, dualOrbitVec_dotProduct_orbitVec, dualOrbitVec_dotProduct_orbitVec,
        show (m * g')⁻¹ * (m * g₂) = g'⁻¹ * g₂ by group]
    have h2 : a₂ * (dualOrbitVec ρ w₀ g' ⬝ᵥ orbitVec ρ e g₂) ≠ 0 := by
      rw [← smul_eq_mul, ← dotProduct_smul, ← hg₂, hb', smul_dotProduct, smul_eq_mul]
      exact mul_ne_zero hb'ne hξ₀m
    have h3 : ξ ⬝ᵥ orbitVec ρ e g₁ ≠ 0 := by
      intro h0
      apply h2
      rw [← h1, hcw, dotProduct_smul, h0, smul_zero, mul_zero]
    rw [hg₁, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero ha₁ h3
  -- (8) `ξ` is a torus eigenvector, hence pairs with `ρ(g) e` as with its lowest-weight part.
  have heig : ∀ s : I → kˣ, ∃ c : k, (ξ ᵥ* (P : Matrix ι ι k)) ᵥ*
      diagonal (fun i => (charValue wt s i : k)) = c • (ξ ᵥ* (P : Matrix ι ι k)) := by
    intro s
    obtain ⟨c, hc⟩ := hfix s
    obtain ⟨c', hc'⟩ := dualOrbitVec_eigen ρ hstab hc
    rw [hξ] at hc'
    exact ⟨c', vecMul_diagonal_of_eigen hτ s hc'⟩
  rw [dotProduct_mulVec] at hξ₁
  obtain ⟨i₁, hi₁, hdi₁, -⟩ := exists_of_dotProduct_weightPart_ne_zero hξ₁
  have hlev : ∀ i, (ξ ᵥ* (P : Matrix ι ι k)) i ≠ 0 → d i = cm :=
    fun i hi => (level_eq_of_eigen hd heig hi hi₁).trans hdi₁
  refine ⟨ξ, ?_, ?_⟩
  · rwa [← hv', dotProduct_mulVec, ← dotProduct_weightPart_of_level hlev]
  · -- (9) `ξ` is a `U`-eigenvector.
    intro x hx
    obtain ⟨c, hc⟩ := hU _ hfix x hx
    obtain ⟨c', hc'⟩ := dualOrbitVec_eigen ρ hstab hc
    rw [hξ] at hc'
    have hc'ne : c' ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc'
      exact vecMul_ne_zero (ρ x) hξne hc'
    exact ⟨Units.mk0 c' hc'ne, by rw [Units.val_mk0, hc']⟩

end Core

end Langlands.GroupScheme.FlagCore
