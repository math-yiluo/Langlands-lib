import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Real polynomial functions on `ℂ^ι` and their degree filtration

For a finite type `ι`, `degLE ι d` is the complex span of the monomials of degree `≤ d` in the
real coordinates `v_k` and `conj v_k` of `v : ι → ℂ`. It has dimension at most
`(d + 1)^(2 |ι|)` (`finrank_degLE_le`), is multiplicative (`mul_mem_degLE`), and the derivative
of an element of degree `≤ d` along a polynomial vector field of degree `≤ e` has degree
`≤ d + e` (`fderiv_apply_mem_degLE`).
-/

noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.RealPolynomialFunctions

variable (ι : Type*) [Fintype ι]

/-- The real coordinates of `v : ι → ℂ`: `v k` for `(k, false)` and `conj (v k)` for
`(k, true)`. -/
def coord (c : ι × Bool) (v : ι → ℂ) : ℂ :=
  if c.2 then conj (v c.1) else v c.1

/-- The monomial `∏_c coord_c^(α c)`. -/
def mono (α : ι × Bool → ℕ) (v : ι → ℂ) : ℂ :=
  ∏ c, coord ι c v ^ α c

/-- The span of the monomials of degree `≤ d`. -/
def degLE (d : ℕ) : Submodule ℂ ((ι → ℂ) → ℂ) :=
  Submodule.span ℂ {f | ∃ α : ι × Bool → ℕ, ∑ c, α c ≤ d ∧ f = mono ι α}

variable {ι}

theorem mono_mem_degLE {α : ι × Bool → ℕ} {d : ℕ} (h : ∑ c, α c ≤ d) : mono ι α ∈ degLE ι d :=
  Submodule.subset_span ⟨α, h, rfl⟩

theorem degLE_mono {a b : ℕ} (hab : a ≤ b) : degLE ι a ≤ degLE ι b :=
  Submodule.span_mono fun _ ⟨α, hα, he⟩ => ⟨α, hα.trans hab, he⟩

theorem one_mem_degLE (d : ℕ) : (fun _ => (1 : ℂ)) ∈ degLE ι d := by
  have : mono ι 0 = fun _ => (1 : ℂ) := by
    funext v; simp [mono]
  rw [← this]
  exact mono_mem_degLE (by simp)

theorem const_mem_degLE (a : ℂ) (d : ℕ) : (fun _ => a) ∈ degLE ι d := by
  have e : (fun _ : ι → ℂ => a) = a • fun _ => (1 : ℂ) := by
    funext v; simp
  rw [e]
  exact (degLE ι d).smul_mem a (one_mem_degLE d)

theorem coord_mem_degLE (c : ι × Bool) : coord ι c ∈ degLE ι 1 := by
  classical
  have : mono ι (Pi.single c 1) = coord ι c := by
    funext v
    simp only [mono]
    rw [Finset.prod_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [← this]
  exact mono_mem_degLE (by simp)

theorem mono_mul (α β : ι × Bool → ℕ) : mono ι α * mono ι β = mono ι (α + β) := by
  funext v
  simp only [Pi.mul_apply, mono, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- Products of elements of degree `≤ a` and `≤ b` have degree `≤ a + b`. -/
theorem mul_mem_degLE {a b : ℕ} {f g : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι a) (hg : g ∈ degLE ι b) :
    f * g ∈ degLE ι (a + b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, hα, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨β, hβ, rfl⟩ := hg
      rw [mono_mul]
      refine mono_mem_degLE ?_
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      omega
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- **Dimension bound.** -/
theorem finrank_degLE_le (d : ℕ) :
    Module.finrank ℂ (degLE ι d) ≤ (d + 1) ^ Fintype.card (ι × Bool) := by
  classical
  let b : (ι × Bool → Fin (d + 1)) → ((ι → ℂ) → ℂ) := fun β => mono ι fun c => (β c : ℕ)
  have hle : degLE ι d ≤ Submodule.span ℂ (Set.range b) := by
    refine Submodule.span_le.2 fun f ⟨α, hα, hf⟩ => Submodule.subset_span ⟨fun c =>
      ⟨α c, Nat.lt_succ_of_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)).trans hα)⟩, ?_⟩
    rw [hf]
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_range_le_card (R := ℂ) b
  rw [Fintype.card_fun, Fintype.card_fin] at h2
  exact h1.trans h2

instance degLE_finiteDimensional (d : ℕ) : FiniteDimensional ℂ (degLE ι d) := by
  classical
  let b : (ι × Bool → Fin (d + 1)) → ((ι → ℂ) → ℂ) := fun β => mono ι fun c => (β c : ℕ)
  have hle : degLE ι d ≤ Submodule.span ℂ (Set.range b) := by
    refine Submodule.span_le.2 fun f ⟨α, hα, hf⟩ => Submodule.subset_span ⟨fun c =>
      ⟨α c, Nat.lt_succ_of_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)).trans hα)⟩, ?_⟩
    rw [hf]
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  exact Submodule.finiteDimensional_of_le hle

/-! ## Derivatives -/

/-- `f` is differentiable and its derivative along every vector field of degree `≤ e` has
degree `≤ d + e`. -/
def DerivDeg (d : ℕ) (f : (ι → ℂ) → ℂ) : Prop :=
  Differentiable ℝ f ∧ ∀ (e : ℕ) (W : (ι → ℂ) → (ι → ℂ)), (∀ c, coord ι c ∘ W ∈ degLE ι e) →
    (fun v => fderiv ℝ f v (W v)) ∈ degLE ι (d + e)

/-- The real-linear coordinate functional. -/
def coordCLM (c : ι × Bool) : (ι → ℂ) →L[ℝ] ℂ :=
  if c.2 then Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj c.1)
  else (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) c.1)

omit [Fintype ι] in
theorem coordCLM_apply (c : ι × Bool) (v : ι → ℂ) : coordCLM c v = coord ι c v := by
  unfold coordCLM coord
  split_ifs <;> simp

theorem derivDeg_coord (c : ι × Bool) : DerivDeg 1 (coord ι c) := by
  have he : coord ι c = coordCLM c := funext fun v => (coordCLM_apply c v).symm
  refine ⟨?_, fun e W hW => ?_⟩
  · rw [he]; exact (coordCLM c).differentiable
  · have : (fun v => fderiv ℝ (coord ι c) v (W v)) = coord ι c ∘ W := by
      funext v
      rw [he, ContinuousLinearMap.fderiv, Function.comp_apply, coordCLM_apply]
    rw [this]
    exact degLE_mono (by omega) (hW c)

theorem derivDeg_const (a : ℂ) (d : ℕ) : DerivDeg d (fun _ : ι → ℂ => a) := by
  refine ⟨differentiable_const a, fun e W _ => ?_⟩
  have : (fun v => fderiv ℝ (fun _ : ι → ℂ => a) v (W v)) = 0 := by
    funext v; simp
  rw [this]
  exact Submodule.zero_mem _

theorem DerivDeg.mono {a b : ℕ} {f : (ι → ℂ) → ℂ} (hf : DerivDeg a f) (hab : a ≤ b) :
    DerivDeg b f :=
  ⟨hf.1, fun e W hW => degLE_mono (by omega) (hf.2 e W hW)⟩

theorem DerivDeg.add {d : ℕ} {f g : (ι → ℂ) → ℂ} (hf : DerivDeg d f) (hg : DerivDeg d g) :
    DerivDeg d (f + g) := by
  refine ⟨hf.1.add hg.1, fun e W hW => ?_⟩
  have : (fun v => fderiv ℝ (f + g) v (W v)) =
      (fun v => fderiv ℝ f v (W v)) + fun v => fderiv ℝ g v (W v) := by
    funext v
    rw [fderiv_add (hf.1 v) (hg.1 v)]
    rfl
  rw [this]
  exact Submodule.add_mem _ (hf.2 e W hW) (hg.2 e W hW)

theorem DerivDeg.smul {d : ℕ} {f : (ι → ℂ) → ℂ} (hf : DerivDeg d f) (r : ℂ) :
    DerivDeg d (r • f) := by
  refine ⟨?_, fun e W hW => ?_⟩
  · exact (hf.1.const_smul r)
  · have : (fun v => fderiv ℝ (r • f) v (W v)) = r • fun v => fderiv ℝ f v (W v) := by
      funext v
      rw [fderiv_const_smul (hf.1 v)]
      rfl
    rw [this]
    exact Submodule.smul_mem _ r (hf.2 e W hW)

theorem DerivDeg.mul {a b : ℕ} {f g : (ι → ℂ) → ℂ} (hf : DerivDeg a f) (hg : DerivDeg b g)
    (hf' : f ∈ degLE ι a) (hg' : g ∈ degLE ι b) : DerivDeg (a + b) (f * g) := by
  refine ⟨hf.1.mul hg.1, fun e W hW => ?_⟩
  have : (fun v => fderiv ℝ (f * g) v (W v)) =
      f * (fun v => fderiv ℝ g v (W v)) + g * fun v => fderiv ℝ f v (W v) := by
    funext v
    rw [fderiv_mul (hf.1 v) (hg.1 v)]
    simp [smul_eq_mul]
  rw [this]
  refine Submodule.add_mem _ ?_ ?_
  · have := mul_mem_degLE hf' (hg.2 e W hW)
    exact degLE_mono (by omega) this
  · have := mul_mem_degLE hg' (hf.2 e W hW)
    exact degLE_mono (by omega) this

theorem derivDeg_mono (α : ι × Bool → ℕ) : DerivDeg (∑ c, α c) (mono ι α) := by
  classical
  have hpow : ∀ (c : ι × Bool) (k : ℕ), DerivDeg k (fun v => coord ι c v ^ k) ∧
      (fun v => coord ι c v ^ k) ∈ degLE ι k := by
    intro c k
    induction k with
    | zero =>
      simp only [pow_zero]
      exact ⟨derivDeg_const 1 0, one_mem_degLE 0⟩
    | succ k ih =>
      have h1 : (fun v => coord ι c v ^ (k + 1)) = (fun v => coord ι c v ^ k) * coord ι c := by
        funext v; simp [pow_succ]
      rw [h1]
      exact ⟨ih.1.mul (derivDeg_coord c) ih.2 (coord_mem_degLE c),
        mul_mem_degLE ih.2 (coord_mem_degLE c)⟩
  have key : ∀ s : Finset (ι × Bool), DerivDeg (∑ c ∈ s, α c) (fun v => ∏ c ∈ s, coord ι c v ^ α c)
      ∧ (fun v => ∏ c ∈ s, coord ι c v ^ α c) ∈ degLE ι (∑ c ∈ s, α c) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact ⟨derivDeg_const 1 0, one_mem_degLE 0⟩
    | insert c s hc ih =>
      simp only [Finset.prod_insert hc, Finset.sum_insert hc]
      have h1 : (fun v => coord ι c v ^ α c * ∏ x ∈ s, coord ι x v ^ α x) =
          (fun v => coord ι c v ^ α c) * fun v => ∏ x ∈ s, coord ι x v ^ α x := rfl
      rw [h1]
      exact ⟨(hpow c (α c)).1.mul ih.1 (hpow c (α c)).2 ih.2,
        mul_mem_degLE (hpow c (α c)).2 ih.2⟩
  exact (key Finset.univ).1

/-- **Derivatives lower nothing and raise the degree by at most the degree of the vector field.**
Every element of `degLE ι d` is differentiable, and its derivative along a vector field whose
coordinates have degree `≤ e` has degree `≤ d + e`. -/
theorem derivDeg_of_mem {d : ℕ} {f : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι d) : DerivDeg d f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, hα, rfl⟩ := hf
    exact (derivDeg_mono α).mono hα
  | zero => exact derivDeg_const (ι := ι) 0 d
  | add x y _ _ hx hy => exact hx.add hy
  | smul r x _ hx => exact hx.smul r

theorem fderiv_apply_mem_degLE {d e : ℕ} {f : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι d)
    {W : (ι → ℂ) → (ι → ℂ)} (hW : ∀ c, coord ι c ∘ W ∈ degLE ι e) :
    (fun v => fderiv ℝ f v (W v)) ∈ degLE ι (d + e) :=
  (derivDeg_of_mem hf).2 e W hW

/-! ## Powers, conjugates and composition -/

theorem pow_mem_degLE {a : ℕ} {f : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι a) (k : ℕ) :
    f ^ k ∈ degLE ι (k * a) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_mul]
    exact one_mem_degLE 0
  | succ k ih =>
    rw [pow_succ, add_mul, one_mul]
    exact mul_mem_degLE ih hf

theorem prod_mem_degLE {κ : Type*} (s : Finset κ) (f : κ → (ι → ℂ) → ℂ) (a : κ → ℕ)
    (hf : ∀ k ∈ s, f k ∈ degLE ι (a k)) : (∏ k ∈ s, f k) ∈ degLE ι (∑ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact one_mem_degLE 0
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    exact mul_mem_degLE (hf k (Finset.mem_insert_self k s))
      (ih fun k' hk' => hf k' (Finset.mem_insert_of_mem hk'))

/-- Swapping the holomorphic and antiholomorphic coordinates. -/
def swapEquiv : ι × Bool ≃ ι × Bool where
  toFun c := (c.1, !c.2)
  invFun c := (c.1, !c.2)
  left_inv c := by simp
  right_inv c := by simp

theorem conj_mono (α : ι × Bool → ℕ) :
    (fun v => conj (mono ι α v)) = mono ι (fun c => α (c.1, !c.2)) := by
  funext v
  simp only [mono, map_prod, map_pow]
  refine Fintype.prod_equiv swapEquiv _ _ fun c => ?_
  rcases c with ⟨k, b⟩
  cases b <;> simp [coord, swapEquiv]

/-- Complex conjugates of elements of degree `≤ d` have degree `≤ d`. -/
theorem conj_mem_degLE {d : ℕ} {f : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι d) :
    (fun v => conj (f v)) ∈ degLE ι d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, hα, rfl⟩ := hf
    rw [conj_mono]
    refine mono_mem_degLE ?_
    calc ∑ c, α (c.1, !c.2) = ∑ c, α c :=
          Fintype.sum_equiv swapEquiv _ _ fun c => rfl
      _ ≤ d := hα
  | zero =>
    have : (fun v => conj ((0 : (ι → ℂ) → ℂ) v)) = 0 := by
      funext v; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun v => conj ((x + y) v)) = (fun v => conj (x v)) + fun v => conj (y v) := by
      funext v; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have : (fun v => conj ((r • x) v)) = conj r • fun v => conj (x v) := by
      funext v; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

variable {ι' : Type*} [Fintype ι']

/-- **Composition with a polynomial map.** If every real coordinate of `W` has degree `≤ e`,
then `P ∘ W` has degree `≤ d e` for `P` of degree `≤ d`. -/
theorem comp_mem_degLE {d e : ℕ} {P : (ι → ℂ) → ℂ} (hP : P ∈ degLE ι d)
    {W : (ι' → ℂ) → (ι → ℂ)} (hW : ∀ c, coord ι c ∘ W ∈ degLE ι' e) :
    P ∘ W ∈ degLE ι' (d * e) := by
  induction hP using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, hα, rfl⟩ := hf
    have h1 : mono ι α ∘ W = ∏ c, (coord ι c ∘ W) ^ α c := by
      funext v; simp [mono, Finset.prod_apply]
    rw [h1]
    have := prod_mem_degLE (ι := ι') Finset.univ (fun c => (coord ι c ∘ W) ^ α c)
      (fun c => α c * e) fun c _ => pow_mem_degLE (hW c) (α c)
    refine degLE_mono ?_ this
    rw [← Finset.sum_mul]
    exact Nat.mul_le_mul_right e hα
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ r hx

omit [Fintype ι] in
/-- The coordinates of a map all of whose holomorphic coordinates have degree `≤ e` have
degree `≤ e` (the antiholomorphic ones are their conjugates). -/
theorem coord_comp_mem_degLE {e : ℕ} {W : (ι' → ℂ) → (ι → ℂ)}
    (hW : ∀ k, (fun v => W v k) ∈ degLE ι' e) (c : ι × Bool) :
    coord ι c ∘ W ∈ degLE ι' e := by
  rcases c with ⟨k, b⟩
  cases b
  · exact hW k
  · exact conj_mem_degLE (hW k)

end Langlands.Archimedean.RealPolynomialFunctions
