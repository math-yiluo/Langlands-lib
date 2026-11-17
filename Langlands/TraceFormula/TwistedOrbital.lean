import Langlands.Analysis.Local.QuotientMeasure
import Langlands.Analysis.Local.QuotientAutomorphismStatement
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Twisted conjugation, twisted centralizers and twisted orbital integrals

Generic definitions for the simple (twisted) trace formula, following
Getz–Hahn, *An introduction to automorphic representations*, §18.5
(printed pp. 486–488): an endomorphism `θ` of a group `G` acts on `G` by
`θ`-twisted conjugation `(x, δ) ↦ x⁻¹ * δ * θ x`; the `θ`-centralizer of `δ` is
its stabilizer; the `θ`-twisted orbital integral of `f` at `δ` integrates
`x ↦ f (x⁻¹ * δ * θ x)` over the actual left coset space of the
`θ`-centralizer against a supplied measure. The trivial twist recovers
ordinary conjugation, centralizers and orbital integrals.

For any subgroup `Γ`, the twisted geometric kernel expression is
`K(x, y) = ∑' γ : Γ, f (x⁻¹ * γ * θ y)`. Under the analytic hypotheses of
Getz–Hahn §18.5 this is the kernel of `R(f) ∘ I_θ`, where
`I_θ φ = φ ∘ θ⁻¹`. This module defines the expression and the inverse-pullback
operator, without proving an integral-kernel identity or a trace formula.

The source specializes to finite-order automorphisms of reductive groups and
uses adelic quotients by split central groups. Here the algebraic definitions
allow any group endomorphism and all quotient measures are explicit parameters.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration

universe uG uF

section Algebra

variable {G : Type uG} [Group G] {F : Type uF} [FunLike F G G] [MonoidHomClass F G G]

/-- `θ`-twisted conjugation of `δ` by `x`: `x⁻¹ * δ * θ x`. -/
def twistedConj (θ : F) (x δ : G) : G :=
  x⁻¹ * δ * θ x

omit [MonoidHomClass F G G] in
@[simp] theorem twistedConj_apply (θ : F) (x δ : G) :
    twistedConj θ x δ = x⁻¹ * δ * θ x := rfl

@[simp] theorem twistedConj_one (θ : F) (δ : G) : twistedConj θ 1 δ = δ := by
  simp [twistedConj]

/-- Twisted conjugation is a right action: conjugating by `x`, then by `y`, is
conjugating by `x * y`. -/
theorem twistedConj_mul (θ : F) (x y δ : G) :
    twistedConj θ y (twistedConj θ x δ) = twistedConj θ (x * y) δ := by
  simp [twistedConj, mul_assoc]

/-- The `θ`-centralizer `{x | x⁻¹ * δ * θ x = δ}` of `δ`. -/
def twistedCentralizer (θ : F) (δ : G) : Subgroup G where
  carrier := {x | x⁻¹ * δ * θ x = δ}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    calc (x * y)⁻¹ * δ * θ (x * y) = y⁻¹ * (x⁻¹ * δ * θ x) * θ y := by
          simp [mul_assoc]
      _ = δ := by rw [hx, hy]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have h : δ * θ x = x * δ := by
      calc δ * θ x = x * (x⁻¹ * δ * θ x) := by simp [mul_assoc]
        _ = x * δ := by rw [hx]
    have h' : θ x = δ⁻¹ * (x * δ) := by rw [← h]; group
    calc x⁻¹⁻¹ * δ * θ x⁻¹ = x * δ * (θ x)⁻¹ := by simp [map_inv]
      _ = δ := by rw [h']; group

theorem mem_twistedCentralizer (θ : F) (δ x : G) :
    x ∈ twistedCentralizer θ δ ↔ x⁻¹ * δ * θ x = δ := Iff.rfl

/-- The twisted conjugate `x⁻¹ * δ * θ x` depends only on the coset
`twistedCentralizer θ δ * x`. -/
theorem twistedConj_left_mul (θ : F) (δ : G) (c : twistedCentralizer θ δ) (x : G) :
    (c.val * x)⁻¹ * δ * θ (c.val * x) = x⁻¹ * δ * θ x := by
  have hc : c.val⁻¹ * δ * θ c.val = δ := c.property
  calc (c.val * x)⁻¹ * δ * θ (c.val * x)
      = x⁻¹ * (c.val⁻¹ * δ * θ c.val) * θ x := by simp [mul_assoc]
    _ = x⁻¹ * δ * θ x := by rw [hc]

/-- `δ'` is `θ`-conjugate to `δ` under the subgroup `H`: `δ' = h⁻¹ * δ * θ h`
for some `h ∈ H`. -/
def IsTwistedConjugate (H : Subgroup G) (θ : F) (δ δ' : G) : Prop :=
  ∃ h ∈ H, h⁻¹ * δ * θ h = δ'

/-- The `θ`-conjugacy class `{h⁻¹ * δ * θ h | h ∈ H}` of `δ` under `H`. -/
def twistedClass (H : Subgroup G) (θ : F) (δ : G) : Set G :=
  {δ' | IsTwistedConjugate H θ δ δ'}

omit [MonoidHomClass F G G] in
theorem mem_twistedClass (H : Subgroup G) (θ : F) (δ δ' : G) :
    δ' ∈ twistedClass H θ δ ↔ ∃ h ∈ H, h⁻¹ * δ * θ h = δ' := Iff.rfl

/-- The `θ`-twisted conjugate integrand `x ↦ f (x⁻¹ * δ * θ x)`, descended to
the left coset space of the `θ`-centralizer. -/
def twistedOrbitFunction (θ : F) (δ : G) {A : Type*} (f : G → A) :
    LeftQuotient (twistedCentralizer θ δ) → A :=
  descend (twistedCentralizer θ δ) (fun x => f (x⁻¹ * δ * θ x))
    (fun c x => by simp only [twistedConj_left_mul])

@[simp] theorem twistedOrbitFunction_mk (θ : F) (δ : G) {A : Type*} (f : G → A) (x : G) :
    twistedOrbitFunction θ δ f (Quotient.mk _ x) = f (x⁻¹ * δ * θ x) := rfl

/-- The trivially twisted centralizer is the ordinary centralizer. -/
theorem twistedCentralizer_id (δ : G) :
    twistedCentralizer (MonoidHom.id G) δ = Subgroup.centralizer {δ} := by
  ext x
  rw [mem_twistedCentralizer, Subgroup.mem_centralizer_singleton_iff]
  simp only [MonoidHom.id_apply]
  constructor
  · intro h
    calc x * δ = x * (x⁻¹ * δ * x) := by rw [h]
      _ = δ * x := by group
  · intro h
    calc x⁻¹ * δ * x = x⁻¹ * (x * δ) := by rw [mul_assoc, ← h]
      _ = δ := by group

end Algebra

section Integral

variable {G : Type uG} [Group G]
variable {F : Type uF} [FunLike F G G] [MonoidHomClass F G G]

/-- The `θ`-twisted orbital integral of `f` at `δ` with respect to a supplied
measure `ν` on the actual left coset space `twistedCentralizer θ δ \ G`:
`∫ f (x⁻¹ * δ * θ x) dν(x)`, the generic group version of Getz–Hahn (18.32).
This is Mathlib's total Bochner integral, equal to zero if the descended
integrand is not `ν`-integrable. No normalization of `ν` is built in. -/
def twistedOrbitalIntegral (θ : F) (δ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G → ℂ) : ℂ :=
  ∫ q, twistedOrbitFunction θ δ f q ∂ν

/-- The ordinary orbital integral `∫ f (x⁻¹ * δ * x) dν(x)` over the left coset
space of the centralizer: the twisted orbital integral for the trivial twist. -/
abbrev orbitalIntegral (δ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id G) δ))) (f : G → ℂ) : ℂ :=
  twistedOrbitalIntegral (MonoidHom.id G) δ ν f

end Integral

section Kernel

variable {G : Type uG} [Group G]
variable {F : Type uF} [FunLike F G G] [MonoidHomClass F G G]

/-- The twisted geometric kernel expression
`K(x, y) = ∑' γ : Γ, f (x⁻¹ * γ * θ y)`, following Getz–Hahn §18.5.
It is Mathlib's unconditional sum, equal to zero for a nonsummable family.
Identifying it with the kernel of `R(f) ∘ I_θ` requires analytic hypotheses. -/
def twistedKernel (Γ : Subgroup G) (θ : F) (f : G → ℂ) (x y : G) : ℂ :=
  ∑' γ : Γ, f (x⁻¹ * γ.val * θ y)

omit [MonoidHomClass F G G] in
/-- The kernel is invariant under left translation of its first variable
by `Γ`. -/
theorem twistedKernel_left_mul_left (Γ : Subgroup G) (θ : F) (f : G → ℂ)
    (γ : Γ) (x y : G) :
    twistedKernel Γ θ f (γ.val * x) y = twistedKernel Γ θ f x y := by
  unfold twistedKernel
  refine (Equiv.tsum_eq (Equiv.mulLeft γ) _).symm.trans ?_
  congr 1
  funext η
  simp [mul_assoc]

/-- The kernel is invariant under left translation of its second variable by
`Γ` when `θ` maps `Γ` into `Γ`. -/
theorem twistedKernel_left_mul_right (Γ : Subgroup G) (θ : F) (f : G → ℂ)
    (hθ : ∀ γ ∈ Γ, θ γ ∈ Γ) (γ : Γ) (x y : G) :
    twistedKernel Γ θ f x (γ.val * y) = twistedKernel Γ θ f x y := by
  unfold twistedKernel
  let t : Γ := ⟨θ γ.val, hθ γ.val γ.property⟩
  refine (Equiv.tsum_eq (Equiv.mulRight t⁻¹) _).symm.trans ?_
  congr 1
  funext η
  simp [t, mul_assoc]

/-- The diagonal `x ↦ K(x, x)` of the twisted kernel, descended to the left
coset space `Γ \ G`. -/
def twistedKernelDiagonal (Γ : Subgroup G) (θ : F) (hθ : ∀ γ ∈ Γ, θ γ ∈ Γ)
    (f : G → ℂ) : LeftQuotient Γ → ℂ :=
  descend Γ (fun x => twistedKernel Γ θ f x x) (fun γ x => by
    rw [twistedKernel_left_mul_left, twistedKernel_left_mul_right Γ θ f hθ])

@[simp] theorem twistedKernelDiagonal_mk (Γ : Subgroup G) (θ : F)
    (hθ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) (x : G) :
    twistedKernelDiagonal Γ θ hθ f (Quotient.mk _ x) = twistedKernel Γ θ f x x := rfl

end Kernel

section TwistOperator

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The twisting operator `I_θ φ = φ ∘ θ⁻¹` on `L²(Γ \ G, ν)` for a continuous
automorphism `θ` of `G` preserving `Γ`, whose inverse induced homeomorphism
of `Γ \ G` preserves `ν` (Getz–Hahn (18.33)). It is built from Mathlib's
composition linear isometry. -/
def twistOperator (Γ : Subgroup G) (θ : G ≃ₜ* G) (hθ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    [MeasurableSpace (LeftQuotient Γ)] (ν : Measure (LeftQuotient Γ))
    (hν : MeasurePreserving (quotientAutomorphism Γ θ hθ).symm ν ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℂ (quotientAutomorphism Γ θ hθ).symm hν).toContinuousLinearMap

theorem twistOperator_coeFn (Γ : Subgroup G) (θ : G ≃ₜ* G)
    (hθ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    [MeasurableSpace (LeftQuotient Γ)] (ν : Measure (LeftQuotient Γ))
    (hν : MeasurePreserving (quotientAutomorphism Γ θ hθ).symm ν ν) (φ : Lp ℂ 2 ν) :
    (twistOperator Γ θ hθ ν hν φ : LeftQuotient Γ → ℂ) =ᵐ[ν]
      fun q => φ ((quotientAutomorphism Γ θ hθ).symm q) :=
  Lp.coeFn_compMeasurePreserving φ hν

theorem norm_twistOperator_apply (Γ : Subgroup G) (θ : G ≃ₜ* G)
    (hθ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    [MeasurableSpace (LeftQuotient Γ)] (ν : Measure (LeftQuotient Γ))
    (hν : MeasurePreserving (quotientAutomorphism Γ θ hθ).symm ν ν) (φ : Lp ℂ 2 ν) :
    ‖twistOperator Γ θ hθ ν hν φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving φ hν

end TwistOperator

end Langlands.TraceFormula
