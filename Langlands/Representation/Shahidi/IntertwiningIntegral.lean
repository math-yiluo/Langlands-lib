import Langlands.Representation.Shahidi.Geometry
import Langlands.HarmonicAnalysis.SmoothWeakIntegral
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! # Shahidi's intertwining integral on functions, as a smooth weak integral -/

noncomputable section

open MeasureTheory
open scoped NNReal

universe uX uF uH uV

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

variable {X : Type uX} [MeasurableSpace X]
variable {G : Type uH} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} {μ : Measure X} {f : X → V} {v : V}

/-- Translating the values by the group: the test `ℓ ∘ ρ g` is the smooth
functional `ρ̃(g⁻¹) ℓ`. -/
theorem HasIntegral.act [IsTopologicalGroup G] (hf : HasIntegral ρ μ f v) (g : G) :
    HasIntegral ρ μ (fun x => ρ g (f x)) (ρ g v) := by
  intro ℓ
  have h := hf (smoothContragredient ρ g⁻¹ ℓ)
  have hval : ∀ w : V, (smoothContragredient ρ g⁻¹ ℓ).val w = ℓ.val (ρ g w) := by
    intro w
    change ℓ.val (ρ g⁻¹⁻¹ w) = _
    rw [inv_inv]
  simp only [hval] at h
  exact h

/-- Change of variables along a measurable equivalence that rescales the
measure by `c`. -/
theorem HasIntegral.comp_measurableEquiv (hf : HasIntegral ρ μ f v) (e : X ≃ᵐ X)
    (c : ℝ≥0) (he : μ.map e = c • μ) :
    HasIntegral ρ μ (fun x => f (e x)) ((c : ℂ) • v) := by
  intro ℓ
  obtain ⟨hi, hv⟩ := hf ℓ
  refine ⟨?_, ?_⟩
  · have hmap : MeasureTheory.Integrable (fun x => ℓ.val (f x)) (μ.map e) := by
      rw [he]
      exact hi.smul_measure ENNReal.coe_ne_top
    exact (integrable_map_equiv e _).1 hmap
  · rw [← integral_map_equiv e (fun x => ℓ.val (f x)), he, integral_smul_nnreal_measure, hv,
      map_smul, NNReal.smul_def, Complex.real_smul]
    simp

end Langlands.HarmonicAnalysis.SmoothWeakIntegral

namespace Langlands.Shahidi

open HarmonicAnalysis GeneralLinear

section Integrand

variable {F : Type uF} [Field F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (m n : ℕ)

/-- The integrand of Shahidi's (0.1) at `g`: `a ↦ f(w_(m,n) u'(a) g)`, in the
rectangular coordinates of `U'`. -/
def intertwiningIntegrand (g : Langlands.GeneralLinear (m + n) F) :
    (Langlands.GeneralLinear (m + n) F → V) →ₗ[ℂ] (Matrix (Fin n) (Fin m) F → V) where
  toFun f a := f (blockWeyl m n F * intertwiningUnipotent m n F a * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem intertwiningIntegrand_apply (g : Langlands.GeneralLinear (m + n) F)
    (f : Langlands.GeneralLinear (m + n) F → V) (a : Matrix (Fin n) (Fin m) F) :
    intertwiningIntegrand m n g f a =
      f (blockWeyl m n F * intertwiningUnipotent m n F a * g) := rfl

/-- Right translation of the function is right translation of the point. -/
theorem intertwiningIntegrand_rightTranslate (g h : Langlands.GeneralLinear (m + n) F)
    (f : Langlands.GeneralLinear (m + n) F → V) :
    intertwiningIntegrand m n g (fun x => f (x * h)) = intertwiningIntegrand m n (g * h) f := by
  funext a
  simp [mul_assoc]

/-- Left translation of the point by `u'(b)` shifts the coordinate by `b`. -/
theorem intertwiningIntegrand_unipotent_mul (b : Matrix (Fin n) (Fin m) F)
    (g : Langlands.GeneralLinear (m + n) F) (f : Langlands.GeneralLinear (m + n) F → V) :
    intertwiningIntegrand m n (intertwiningUnipotent m n F b * g) f =
      fun a => intertwiningIntegrand m n g f (a + b) := by
  funext a
  simp [intertwiningUnipotent_add, mul_assoc]

/-- The upper radical of block sizes `(n,m)` is normalized by the Levi:
`u(a) diag(h₂,h₁) = diag(h₂,h₁) u(h₂⁻¹ a h₁)`. -/
theorem upper_mul_blockSum (a : Matrix (Fin n) (Fin m) F)
    (h₂ : Langlands.GeneralLinear n F) (h₁ : Langlands.GeneralLinear m F) :
    upper n m F a * blockSum (h₂, h₁) =
      blockSum (h₂, h₁) *
        upper n m F (((h₂⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * a *
          (h₁ : Matrix (Fin m) (Fin m) F)) := by
  unfold upper blockSum
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, ← map_mul]
  congr 1
  apply Units.ext
  change Matrix.fromBlocks 1 a 0 1 * Matrix.fromBlocks h₂.val 0 0 h₁.val =
    Matrix.fromBlocks h₂.val 0 0 h₁.val *
      Matrix.fromBlocks 1 (((h₂⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * a *
        (h₁ : Matrix (Fin m) (Fin m) F)) 0 1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end Integrand

section WeakIntegral

open SmoothWeakIntegral

variable {F : Type uF} [Field F] [MeasurableSpace F]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (m n : ℕ) (ρ : Representation ℂ H V) (μ : Measure (Matrix (Fin n) (Fin m) F))

/-- `A` is the intertwining integral (0.1) of `f`: at every point `g`, the
vector `A g` is the weak integral of `a ↦ f(w_(m,n) u'(a) g)` against `μ`,
tested by every smooth functional of `ρ`. -/
def HasIntertwiningIntegral (f A : Langlands.GeneralLinear (m + n) F → V) : Prop :=
  ∀ g, HasIntegral ρ μ (intertwiningIntegrand m n g f) (A g)

/-- The functions whose integral (0.1) has a representing vector at every point. -/
def intertwiningDomain : Submodule ℂ (Langlands.GeneralLinear (m + n) F → V) :=
  ⨅ g, (integrableSubmodule ρ μ).comap (intertwiningIntegrand m n g)

variable {m n ρ μ}

theorem mem_intertwiningDomain {f : Langlands.GeneralLinear (m + n) F → V} :
    f ∈ intertwiningDomain m n ρ μ ↔ ∃ A, HasIntertwiningIntegral m n ρ μ f A := by
  simp only [intertwiningDomain, Submodule.mem_iInf, Submodule.mem_comap,
    mem_integrableSubmodule]
  constructor
  · intro h
    choose A hA using h
    exact ⟨A, hA⟩
  · rintro ⟨A, hA⟩ g
    exact ⟨A g, hA g⟩

theorem hasIntertwiningIntegral_zero :
    HasIntertwiningIntegral m n ρ μ (0 : Langlands.GeneralLinear (m + n) F → V) 0 := by
  intro g
  rw [map_zero]
  exact hasIntegral_zero

theorem HasIntertwiningIntegral.add {f f' A A' : Langlands.GeneralLinear (m + n) F → V}
    (hA : HasIntertwiningIntegral m n ρ μ f A) (hA' : HasIntertwiningIntegral m n ρ μ f' A') :
    HasIntertwiningIntegral m n ρ μ (f + f') (A + A') := by
  intro g
  rw [map_add]
  exact (hA g).add (hA' g)

theorem HasIntertwiningIntegral.smul (c : ℂ) {f A : Langlands.GeneralLinear (m + n) F → V}
    (hA : HasIntertwiningIntegral m n ρ μ f A) :
    HasIntertwiningIntegral m n ρ μ (c • f) (c • A) := by
  intro g
  rw [map_smul]
  exact (hA g).smul c

/-- Right translation of the function translates the integral. -/
theorem HasIntertwiningIntegral.rightTranslate {f A : Langlands.GeneralLinear (m + n) F → V}
    (hA : HasIntertwiningIntegral m n ρ μ f A) (h : Langlands.GeneralLinear (m + n) F) :
    HasIntertwiningIntegral m n ρ μ (fun x => f (x * h)) (fun x => A (x * h)) := by
  intro g
  rw [intertwiningIntegrand_rightTranslate]
  exact hA (g * h)

theorem rightTranslate_mem_intertwiningDomain {f : Langlands.GeneralLinear (m + n) F → V}
    (hf : f ∈ intertwiningDomain m n ρ μ) (h : Langlands.GeneralLinear (m + n) F) :
    (fun x => f (x * h)) ∈ intertwiningDomain m n ρ μ := by
  obtain ⟨A, hA⟩ := mem_intertwiningDomain.1 hf
  exact mem_intertwiningDomain.2 ⟨_, hA.rightTranslate h⟩

/-- Translation-invariant coordinates on `U'`: left translation of the point
by `u'(b)` does not change the integral. -/
theorem HasIntertwiningIntegral.unipotent_mul [MeasurableAdd F] [μ.IsAddLeftInvariant]
    {f A : Langlands.GeneralLinear (m + n) F → V} (hA : HasIntertwiningIntegral m n ρ μ f A)
    (b : Matrix (Fin n) (Fin m) F) (g : Langlands.GeneralLinear (m + n) F) :
    HasIntegral ρ μ (intertwiningIntegrand m n (intertwiningUnipotent m n F b * g) f) (A g) := by
  have hmeas (c : Matrix (Fin n) (Fin m) F) :
      Measurable (fun a : Matrix (Fin n) (Fin m) F => a + c) :=
    Matrix.measurable_iff.2 fun i j => Matrix.measurable_apply.add_const (c i j)
  let e : Matrix (Fin n) (Fin m) F ≃ᵐ Matrix (Fin n) (Fin m) F :=
    { toFun := fun a => a + b
      invFun := fun a => a + -b
      left_inv := fun a => add_neg_cancel_right a b
      right_inv := fun a => neg_add_cancel_right a b
      measurable_toFun := hmeas b
      measurable_invFun := hmeas (-b) }
  have he : μ.map e = (1 : ℝ≥0) • μ := by
    rw [one_smul]
    change μ.map (fun a => a + b) = μ
    simp_rw [add_comm _ b]
    exact map_add_left_eq_self μ b
  have h := (hA g).comp_measurableEquiv e 1 he
  rw [show ((1 : ℝ≥0) : ℂ) = 1 by simp, one_smul] at h
  rw [intertwiningIntegrand_unipotent_mul]
  exact h

/-- Levi covariance. If `f(diag(h₁,h₂) x) = z • ρ(h) f(x)` and the change of
variables `a ↦ h₂⁻¹ a h₁` multiplies `μ` by `c`, then the integral at
`diag'(h₂,h₁) x` in the swapped block order is `z c ρ(h)` applied to the
integral at `x`. -/
theorem HasIntertwiningIntegral.levi [IsTopologicalGroup H]
    {f A : Langlands.GeneralLinear (m + n) F → V} (hA : HasIntertwiningIntegral m n ρ μ f A)
    (h₁ : Langlands.GeneralLinear m F) (h₂ : Langlands.GeneralLinear n F) (h : H) (z : ℂ)
    (hf : ∀ x, f (blockSum (h₁, h₂) * x) = z • ρ h (f x))
    (e : Matrix (Fin n) (Fin m) F ≃ᵐ Matrix (Fin n) (Fin m) F)
    (he : ∀ a, e a = ((h₂⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * a *
      (h₁ : Matrix (Fin m) (Fin m) F))
    (c : ℝ≥0) (hμ : μ.map e = c • μ) (x : Langlands.GeneralLinear (m + n) F) :
    HasIntegral ρ μ (intertwiningIntegrand m n (swapRank m n F (blockSum (h₂, h₁)) * x) f)
      ((z * c) • ρ h (A x)) := by
  have hpt (a : Matrix (Fin n) (Fin m) F) :
      blockWeyl m n F * intertwiningUnipotent m n F a * swapRank m n F (blockSum (h₂, h₁)) =
        blockSum (h₁, h₂) * (blockWeyl m n F * intertwiningUnipotent m n F (e a)) := by
    rw [he, intertwiningUnipotent, intertwiningUnipotent, mul_assoc, ← map_mul,
      upper_mul_blockSum, map_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← blockWeyl_conjugate_blockSum m n F h₂ h₁, inv_mul_cancel_right]
  have hfun : intertwiningIntegrand m n (swapRank m n F (blockSum (h₂, h₁)) * x) f =
      z • fun a => ρ h (intertwiningIntegrand m n x f (e a)) := by
    funext a
    simp only [intertwiningIntegrand_apply, Pi.smul_apply]
    rw [← mul_assoc, hpt, mul_assoc, hf]
  have hval : (z * c) • ρ h (A x) = z • ρ h ((c : ℂ) • A x) := by
    rw [map_smul, smul_smul]
  rw [hfun, hval]
  exact (((hA x).comp_measurableEquiv e c hμ).act h).smul z

section Operator

variable [IsTopologicalGroup H]
variable (hcofinal : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H,
  IsCompact (L : Set H) ∧ L ≤ K) (hρ : IsSmooth ρ)

include hcofinal hρ in
/-- Separation by the smooth dual makes the integral unique. -/
theorem HasIntertwiningIntegral.unique {f A B : Langlands.GeneralLinear (m + n) F → V}
    (hA : HasIntertwiningIntegral m n ρ μ f A) (hB : HasIntertwiningIntegral m n ρ μ f B) :
    A = B :=
  funext fun g => (hA g).unique hcofinal hρ (hB g)

variable (m n ρ μ)

/-- The intertwining operator (0.1), only on its domain of convergence. -/
def intertwiningOperator :
    intertwiningDomain m n ρ μ →ₗ[ℂ] (Langlands.GeneralLinear (m + n) F → V) :=
  LinearMap.pi fun g =>
    (integralLinear hcofinal hρ).comp
      (LinearMap.codRestrict (integrableSubmodule ρ μ)
        ((intertwiningIntegrand m n g).comp (intertwiningDomain m n ρ μ).subtype)
        (fun f => (Submodule.mem_iInf _).1 f.property g))

variable {m n ρ μ}

theorem hasIntertwiningIntegral_intertwiningOperator (f : intertwiningDomain m n ρ μ) :
    HasIntertwiningIntegral m n ρ μ f.val (intertwiningOperator m n ρ μ hcofinal hρ f) :=
  fun g => integralLinear_spec hcofinal hρ
    ⟨intertwiningIntegrand m n g f.val, (Submodule.mem_iInf _).1 f.property g⟩

theorem intertwiningOperator_eq (f : intertwiningDomain m n ρ μ)
    {A : Langlands.GeneralLinear (m + n) F → V} (hA : HasIntertwiningIntegral m n ρ μ f.val A) :
    intertwiningOperator m n ρ μ hcofinal hρ f = A :=
  (hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f).unique hcofinal hρ hA

/-- Every smooth functional of the operator value is the genuine scalar integral. -/
theorem intertwiningOperator_eval (f : intertwiningDomain m n ρ μ)
    (g : Langlands.GeneralLinear (m + n) F) (ℓ : SmoothDual ρ) :
    ℓ.val (intertwiningOperator m n ρ μ hcofinal hρ f g) =
      ∫ a, ℓ.val (f.val (blockWeyl m n F * intertwiningUnipotent m n F a * g)) ∂μ :=
  ((hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f g) ℓ).2.symm

/-- The operator commutes with right translation. -/
theorem intertwiningOperator_rightTranslate (f : intertwiningDomain m n ρ μ)
    (h : Langlands.GeneralLinear (m + n) F) :
    intertwiningOperator m n ρ μ hcofinal hρ
        ⟨fun x => f.val (x * h), rightTranslate_mem_intertwiningDomain f.property h⟩ =
      fun x => intertwiningOperator m n ρ μ hcofinal hρ f (x * h) :=
  intertwiningOperator_eq hcofinal hρ _
    ((hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f).rightTranslate h)

/-- The operator values are left invariant under `U'`. -/
theorem intertwiningOperator_unipotent_mul [MeasurableAdd F] [μ.IsAddLeftInvariant]
    (f : intertwiningDomain m n ρ μ) (b : Matrix (Fin n) (Fin m) F)
    (g : Langlands.GeneralLinear (m + n) F) :
    intertwiningOperator m n ρ μ hcofinal hρ f (intertwiningUnipotent m n F b * g) =
      intertwiningOperator m n ρ μ hcofinal hρ f g :=
  (hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f _).unique hcofinal hρ
    ((hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f).unipotent_mul b g)

/-- The operator values transform under the swapped Levi as in
`HasIntertwiningIntegral.levi`. -/
theorem intertwiningOperator_levi (f : intertwiningDomain m n ρ μ)
    (h₁ : Langlands.GeneralLinear m F) (h₂ : Langlands.GeneralLinear n F) (h : H) (z : ℂ)
    (hf : ∀ x, f.val (blockSum (h₁, h₂) * x) = z • ρ h (f.val x))
    (e : Matrix (Fin n) (Fin m) F ≃ᵐ Matrix (Fin n) (Fin m) F)
    (he : ∀ a, e a = ((h₂⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * a *
      (h₁ : Matrix (Fin m) (Fin m) F))
    (c : ℝ≥0) (hμ : μ.map e = c • μ) (x : Langlands.GeneralLinear (m + n) F) :
    intertwiningOperator m n ρ μ hcofinal hρ f (swapRank m n F (blockSum (h₂, h₁)) * x) =
      (z * c) • ρ h (intertwiningOperator m n ρ μ hcofinal hρ f x) :=
  (hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f _).unique hcofinal hρ
    ((hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f).levi h₁ h₂ h z hf e he c hμ x)

end Operator

end WeakIntegral

end Langlands.Shahidi
