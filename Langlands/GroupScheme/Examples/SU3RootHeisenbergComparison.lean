import Langlands.GroupScheme.Examples.SU3RootParametersRational
import Langlands.GroupScheme.Examples.SU3RootScaling

/-! # Trace-compatible cocycles and quadratic root parameters

Let `L / k` be a separable quadratic extension with conjugation `σ`. A function
`β : L → L → L`, additive in its second argument, is trace compatible if
`β (f x) y + β x (f y) = (f + σ f) β x y` for all `f`, `x` and `y`. Such a function has the
form `β x y = A σ(x) y + B x σ(y)`. If its values have trace zero then `B = -σ(A)`, and if it
is not symmetric then `A + σ(A) ≠ 0`. The Heisenberg law
`(w, x) (w', x') = (w + w' + β x x', x + x')` on trace-zero `w` and arbitrary `x` is then
isomorphic to the law of the quadratic root parameters.
-/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u v

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

local notation "σ" => conjugation k L

/-- Elements fixed by the conjugation lie in the base field. -/
theorem exists_algebraMap_eq_of_conjugation_eq {x : L} (hx : σ x = x) :
    ∃ c : k, algebraMap k L c = x := by
  have : FiniteDimensional k L :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two k L]; decide)
  have h := (IsGalois.mem_range_algebraMap_iff_fixed (F := k) x).2 (fun f => by
    by_cases hf : f = 1
    · rw [hf]
      rfl
    · rw [conjugation_unique k L f hf]
      exact hx)
  exact h

/-- Some element is moved by the conjugation. -/
theorem exists_conjugation_ne : ∃ θ : L, σ θ ≠ θ := by
  by_contra h
  push Not at h
  apply conjugation_ne_one k L
  ext x
  exact h x

/-- Some nonzero element has trace zero. -/
theorem exists_ne_zero_add_conjugation_eq_zero : ∃ x : L, x ≠ 0 ∧ x + σ x = 0 := by
  obtain ⟨θ, hθ⟩ := exists_conjugation_ne k L
  refine ⟨θ - σ θ, sub_ne_zero.2 (Ne.symm hθ), ?_⟩
  rw [map_sub, conjugation_involutive k L θ]
  ring

/-- **Linear maps.** Every `k`-linear map `L → L` is `y ↦ A y + B σ(y)`. -/
theorem exists_eq_add_conjugation_of_linear (ψ : L → L)
    (hadd : ∀ y y', ψ (y + y') = ψ y + ψ y')
    (hsmul : ∀ (c : k) (y : L), ψ (algebraMap k L c * y) = algebraMap k L c * ψ y) :
    ∃ A B : L, ∀ y, ψ y = A * y + B * σ y := by
  obtain ⟨θ, hθ⟩ := exists_conjugation_ne k L
  have hd : σ θ - θ ≠ 0 := sub_ne_zero.2 hθ
  set B := (ψ θ - θ * ψ 1) / (σ θ - θ) with hBdef
  have hB : B * (σ θ - θ) = ψ θ - θ * ψ 1 := div_mul_cancel₀ _ hd
  refine ⟨ψ 1 - B, B, fun y => ?_⟩
  -- write `y = a + b θ` with `a` and `b` fixed by the conjugation
  set b := (y - σ y) / (θ - σ θ) with hbdef
  have hb : b * (θ - σ θ) = y - σ y := div_mul_cancel₀ _ (sub_ne_zero.2 (Ne.symm hθ))
  have hbσ : σ b = b := by
    rw [hbdef, map_div₀, map_sub, map_sub, conjugation_involutive k L y,
      conjugation_involutive k L θ, ← neg_sub y, ← neg_sub θ, neg_div_neg_eq]
  set a := y - b * θ with hadef
  have haσ : σ a = a := by
    rw [hadef, map_sub, map_mul, hbσ]
    linear_combination hb
  obtain ⟨ca, hca⟩ := exists_algebraMap_eq_of_conjugation_eq k L haσ
  obtain ⟨cb, hcb⟩ := exists_algebraMap_eq_of_conjugation_eq k L hbσ
  have hy : y = algebraMap k L ca * 1 + algebraMap k L cb * θ := by
    rw [hca, hcb, hadef]
    ring
  have hyσ : σ y = a + b * σ θ := by
    rw [hy, map_add, map_mul, map_mul, map_one, hca, hcb, haσ, hbσ, mul_one]
  rw [hyσ, hy, hadd, hsmul, hsmul, hca, hcb, mul_one]
  linear_combination (-b) * hB

/-- **Trace-compatible functions.** A function `β : L → L → L`, additive in its second
argument, with `β (f x) y + β x (f y) = (f + σ f) β x y`, is
`β x y = A σ(x) y + B x σ(y)`. -/
theorem exists_eq_of_trace_compatible (β : L → L → L)
    (hadd : ∀ x y y', β x (y + y') = β x y + β x y')
    (htr : ∀ f x y, β (f * x) y + β x (f * y) = (f + σ f) * β x y) :
    ∃ A B : L, ∀ x y, β x y = A * σ x * y + B * x * σ y := by
  set ψ : L → L := fun y => β 1 y with hψdef
  have hβ : ∀ x y, β x y = (x + σ x) * ψ y - ψ (x * y) := by
    intro x y
    have h := htr x 1 y
    rw [mul_one] at h
    simp only [ψ]
    linear_combination h
  have hΔ : ∀ (c : k) (x y : L), (x + σ x) * (ψ (algebraMap k L c * y) -
      algebraMap k L c * ψ y) =
      2 * (ψ (algebraMap k L c * (x * y)) - algebraMap k L c * ψ (x * y)) := by
    intro c x y
    have hl : σ (algebraMap k L c) = algebraMap k L c := (conjugation k L).commutes c
    have h := htr (algebraMap k L c) x y
    rw [hβ (algebraMap k L c * x) y, hβ x (algebraMap k L c * y), hβ x y, map_mul, hl,
      show algebraMap k L c * x * y = algebraMap k L c * (x * y) by ring,
      show x * (algebraMap k L c * y) = algebraMap k L c * (x * y) by ring] at h
    linear_combination h
  have hsmul : ∀ (c : k) (y : L), ψ (algebraMap k L c * y) = algebraMap k L c * ψ y := by
    intro c y
    by_cases h2 : (2 : L) = 0
    · have h := hΔ c (traceOne k L) y
      rw [traceOne_add_conjugate, h2, zero_mul, one_mul] at h
      exact sub_eq_zero.1 h
    · obtain ⟨x, hx0, hx⟩ := exists_ne_zero_add_conjugation_eq_zero k L
      have h := hΔ c x (x⁻¹ * y)
      rw [hx, zero_mul, mul_inv_cancel_left₀ hx0] at h
      exact sub_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left h2)
  obtain ⟨A, B, hAB⟩ := exists_eq_add_conjugation_of_linear k L ψ (hadd 1) hsmul
  refine ⟨A, B, fun x y => ?_⟩
  rw [hβ, hAB, hAB, map_mul]
  ring

/-- Trace-zero values force `B = -σ(A)`. -/
theorem eq_neg_conjugation_of_traceZero {A B : L}
    (h : ∀ x y : L, (A * σ x * y + B * x * σ y) + σ (A * σ x * y + B * x * σ y) = 0) :
    B = -σ A := by
  obtain ⟨θ, hθ⟩ := exists_conjugation_ne k L
  have h1 := h 1 1
  have h2 := h 1 θ
  simp only [map_add, map_mul, map_one, conjugation_involutive k L _] at h1 h2
  have hP : (A + σ B) * (θ - σ θ) = 0 := by
    linear_combination h2 - σ θ * h1
  have hP' : A + σ B = 0 :=
    (mul_eq_zero.1 hP).resolve_right (sub_ne_zero.2 (Ne.symm hθ))
  have := congrArg σ hP'
  rw [map_add, conjugation_involutive k L B, map_zero] at this
  linear_combination this

/-- The normalized cocycle `A σ(x) y - σ(A) x σ(y)`, with values of trace zero. -/
def normalizedCocycle (A : L) (x y : L) : Parameters.traceZero (fieldInvolution k L) :=
  ⟨A * σ x * y - σ A * x * σ y, by
    rw [Parameters.mem_traceZero, fieldInvolution_bar, map_sub, map_mul, map_mul, map_mul, map_mul,
      conjugation_involutive k L A, conjugation_involutive k L x,
      conjugation_involutive k L y]
    ring⟩

@[simp] theorem coe_normalizedCocycle (A x y : L) :
    (normalizedCocycle k L A x y : L) = A * σ x * y - σ A * x * σ y := rfl

/-- **Normal form.** A trace-compatible function with trace-zero values that is not
symmetric is a normalized cocycle with `A + σ(A) ≠ 0`. -/
theorem exists_eq_normalizedCocycle (β : L → L → L)
    (hadd : ∀ x y y', β x (y + y') = β x y + β x y')
    (htr : ∀ f x y, β (f * x) y + β x (f * y) = (f + σ f) * β x y)
    (hzero : ∀ x y, β x y + σ (β x y) = 0) (hnd : ∃ x y, β x y ≠ β y x) :
    ∃ A : L, A + σ A ≠ 0 ∧ ∀ x y, β x y = normalizedCocycle k L A x y := by
  obtain ⟨A, B, hAB⟩ := exists_eq_of_trace_compatible k L β hadd htr
  have hB : B = -σ A :=
    eq_neg_conjugation_of_traceZero k L (fun x y => by rw [← hAB]; exact hzero x y)
  have hform : ∀ x y, β x y = normalizedCocycle k L A x y := by
    intro x y
    rw [hAB, hB, coe_normalizedCocycle]
    ring
  refine ⟨A, fun hA => ?_, hform⟩
  obtain ⟨x, y, hxy⟩ := hnd
  apply hxy
  rw [hform, hform, coe_normalizedCocycle, coe_normalizedCocycle]
  linear_combination (σ x * y - x * σ y) * hA

section Equiv

variable {k L} {A : L}

theorem conjugation_inv_trace : σ ((A + σ A)⁻¹) = (A + σ A)⁻¹ := by
  rw [map_inv₀, map_add, conjugation_involutive k L A, add_comm]

/-- Heisenberg coordinates `(w, x)` for the normalized cocycle of `A`. The point is
`(x, -(A + σ A)⁻¹ w + A (A + σ A)⁻¹ x σ(x))`. -/
def heisenbergParameter (hA : A + σ A ≠ 0) (w : Parameters.traceZero (fieldInvolution k L))
    (x : L) :
    rationalParameters k L :=
  ⟨(x, -(A + σ A)⁻¹ * w + A * (A + σ A)⁻¹ * x * σ x), by
    have hw : (w : L) + σ w = 0 := w.property
    have hs : σ (A + σ A) = A + σ A := by
      rw [map_add, conjugation_involutive k L A, add_comm]
    have hs1 : (A + σ A) * (A + σ A)⁻¹ = 1 := mul_inv_cancel₀ hA
    simp only [fieldInvolution_bar, map_add, map_mul, map_neg, conjugation_inv_trace,
      conjugation_involutive k L x]
    linear_combination (-(A + σ A)⁻¹) * hw + x * σ x * hs1⟩

@[simp] theorem first_heisenbergParameter (hA : A + σ A ≠ 0)
    (w : Parameters.traceZero (fieldInvolution k L)) (x : L) :
    (heisenbergParameter hA w x).first = x := rfl

@[simp] theorem second_heisenbergParameter (hA : A + σ A ≠ 0)
    (w : Parameters.traceZero (fieldInvolution k L)) (x : L) :
    (heisenbergParameter hA w x).second = -(A + σ A)⁻¹ * w + A * (A + σ A)⁻¹ * x * σ x :=
  rfl

/-- The Heisenberg law becomes the law of the quadratic root parameters. -/
theorem heisenbergParameter_mul (hA : A + σ A ≠ 0)
    (w w' : Parameters.traceZero (fieldInvolution k L)) (x x' : L) :
    heisenbergParameter hA w x * heisenbergParameter hA w' x' =
      heisenbergParameter hA (w + w' + normalizedCocycle k L A x x') (x + x') := by
  have hs1 : (A + σ A) * (A + σ A)⁻¹ = 1 := mul_inv_cancel₀ hA
  apply Parameters.ext
  · rfl
  · simp only [Parameters.second_mul, second_heisenbergParameter, first_heisenbergParameter,
      fieldInvolution_bar, AddSubgroup.coe_add, coe_normalizedCocycle, map_add]
    linear_combination (-(x * σ x')) * hs1

/-- Heisenberg coordinates of a quadratic root parameter. -/
def heisenbergCoordinates (p : rationalParameters k L) :
    Parameters.traceZero (fieldInvolution k L) × L :=
  (⟨-(A + σ A) * p.second + A * p.first * σ p.first, by
    have hp : p.second + σ p.second = p.first * σ p.first := p.equation
    rw [Parameters.mem_traceZero, fieldInvolution_bar, map_add, map_mul, map_mul, map_mul, map_neg,
      map_add, conjugation_involutive k L A, conjugation_involutive k L p.first]
    linear_combination (-(A + σ A)) * hp⟩, p.first)

/-- Heisenberg coordinates identify trace-zero elements times `L` with the quadratic root
parameters. -/
def heisenbergEquiv (hA : A + σ A ≠ 0) :
    Parameters.traceZero (fieldInvolution k L) × L ≃ rationalParameters k L where
  toFun p := heisenbergParameter hA p.1 p.2
  invFun := heisenbergCoordinates (A := A)
  left_inv p := by
    have hs1 : (A + σ A) * (A + σ A)⁻¹ = 1 := mul_inv_cancel₀ hA
    obtain ⟨w, x⟩ := p
    refine Prod.ext (Subtype.ext ?_) rfl
    change -(A + σ A) * (-(A + σ A)⁻¹ * w + A * (A + σ A)⁻¹ * x * σ x) + A * x * σ x = w
    linear_combination (w - A * x * σ x) * hs1
  right_inv p := by
    have hs1 : (A + σ A) * (A + σ A)⁻¹ = 1 := mul_inv_cancel₀ hA
    apply Parameters.ext
    · rfl
    · change -(A + σ A)⁻¹ * (-(A + σ A) * p.second + A * p.first * σ p.first) +
        A * (A + σ A)⁻¹ * p.first * σ p.first = p.second
      linear_combination p.second * hs1

@[simp] theorem heisenbergEquiv_apply (hA : A + σ A ≠ 0)
    (w : Parameters.traceZero (fieldInvolution k L)) (x : L) :
    heisenbergEquiv hA (w, x) = heisenbergParameter hA w x := rfl

/-- Scaling `x` by `a` and `w` by `a σ(a)` is the scaling of the root parameters. -/
theorem heisenbergParameter_scale (hA : A + σ A ≠ 0) (a : L)
    (w w' : Parameters.traceZero (fieldInvolution k L)) (x : L)
    (hw : (w' : L) = a * σ a * w) :
    heisenbergParameter hA w' (a * x) = Parameters.scale a (heisenbergParameter hA w x) := by
  apply Parameters.ext
  · rfl
  · simp only [second_heisenbergParameter, Parameters.second_scale, fieldInvolution_bar, hw,
      map_mul]
    ring

/-- The central parameters are those with first Heisenberg coordinate zero. -/
theorem heisenbergParameter_mem_central (hA : A + σ A ≠ 0)
    (w : Parameters.traceZero (fieldInvolution k L)) (x : L) :
    heisenbergParameter hA w x ∈ Parameters.central (fieldInvolution k L) ↔ x = 0 :=
  Parameters.mem_central _

end Equiv

/-- **Comparison with the quadratic root parameters.** Let `β : L → L → L` be additive in
its second argument, trace compatible, with values of trace zero, and not symmetric. Then
there is a bijection `e` from trace-zero elements times `L` to the quadratic root parameters
that turns the Heisenberg law of `β` into the parameter law, has first coordinate `x`, and
turns the scaling `(w, x) ↦ (a σ(a) w, a x)` into `Parameters.scale a`. -/
theorem exists_heisenbergEquiv (β : L → L → L)
    (hadd : ∀ x y y', β x (y + y') = β x y + β x y')
    (htr : ∀ f x y, β (f * x) y + β x (f * y) = (f + σ f) * β x y)
    (hzero : ∀ x y, β x y + σ (β x y) = 0) (hnd : ∃ x y, β x y ≠ β y x) :
    ∃ e : Parameters.traceZero (fieldInvolution k L) × L ≃ rationalParameters k L,
      (∀ (w w' : Parameters.traceZero (fieldInvolution k L)) (x x' : L),
        e (w, x) * e (w', x') = e (w + w' + ⟨β x x', hzero x x'⟩, x + x')) ∧
      (∀ (w : Parameters.traceZero (fieldInvolution k L)) (x : L), (e (w, x)).first = x) ∧
      (∀ (a : L) (w w' : Parameters.traceZero (fieldInvolution k L)) (x : L),
        (w' : L) = a * σ a * w → e (w', a * x) = Parameters.scale a (e (w, x))) := by
  obtain ⟨A, hA, hform⟩ := exists_eq_normalizedCocycle k L β hadd htr hzero hnd
  refine ⟨heisenbergEquiv hA, fun w w' x x' => ?_, fun w x => rfl,
    fun a w w' x hw => heisenbergParameter_scale hA a w w' x hw⟩
  have hβ : (⟨β x x', hzero x x'⟩ : Parameters.traceZero (fieldInvolution k L)) =
      normalizedCocycle k L A x x' := Subtype.ext (hform x x')
  rw [heisenbergEquiv_apply, heisenbergEquiv_apply, heisenbergEquiv_apply, hβ,
    heisenbergParameter_mul]

end Langlands.GroupScheme.SU3Root
