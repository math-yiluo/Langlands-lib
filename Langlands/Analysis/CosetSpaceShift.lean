import Langlands.Group.LeftQuotient
import Langlands.Analysis.L2SlabRecurrence

/-! # Renormalizing shifts on left coset spaces

For a subgroup `H` of a measurable group `A`, the left coset space `H \ A` carries the
quotient (coinduced) σ-algebra. A measure `ν` on `A` pushes forward to `H \ A`. Left
translation by a point `a` normalizing `H` descends to `H \ A`, and an `H`-invariant
function on `A` descends to `H \ A`. If `ν` scales by `k` under left translation by `a` on
`H`-invariant measurable sets, the pushforward scales by `k` under the descended
translation. With a height increased by one, this is an `L2RenormalizingShift`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.CosetSpaceShift

open MeasureTheory Set
open scoped ENNReal NNReal

variable {A : Type*} [Group A] [MeasurableSpace A] (H : Subgroup A)

/-- The left coset space `H \ A`, the quotient by `a ~ b ↔ b a⁻¹ ∈ H`. -/
abbrev Space := Langlands.Induction.LeftQuotient H

/-- The quotient map `A → H \ A`. -/
def mk : A → Space H := Langlands.Induction.quotientMap H

theorem measurable_mk : Measurable (mk H) := fun _ hs => hs

theorem mk_eq_mk_iff {a b : A} : mk H a = mk H b ↔ b * a⁻¹ ∈ H :=
  Quotient.eq.trans QuotientGroup.rightRel_apply

theorem mk_mul {h : A} (hh : h ∈ H) (g : A) : mk H (h * g) = mk H g := by
  rw [mk_eq_mk_iff]
  simpa using H.inv_mem hh

theorem measurable_of_comp {β : Type*} [MeasurableSpace β] {f : Space H → β}
    (hf : Measurable (f ∘ mk H)) : Measurable f := fun _ hs => hf hs

/-- Descent of an `H`-invariant function. -/
def lift {β : Type*} (φ : A → β) (hφ : ∀ h ∈ H, ∀ g, φ (h * g) = φ g) : Space H → β :=
  Langlands.QuotientIntegration.descend H φ (fun h => hφ h h.property)

@[simp] theorem lift_mk {β : Type*} (φ : A → β) (hφ : ∀ h ∈ H, ∀ g, φ (h * g) = φ g) (g : A) :
    lift H φ hφ (mk H g) = φ g := rfl

theorem measurable_lift {β : Type*} [MeasurableSpace β] {φ : A → β}
    (hφ : ∀ h ∈ H, ∀ g, φ (h * g) = φ g) (hm : Measurable φ) : Measurable (lift H φ hφ) :=
  measurable_of_comp H hm

/-- Integrals of descended functions against the pushforward measure. -/
theorem lintegral_lift (ν : Measure A) {φ : A → ℝ≥0∞} (hφ : ∀ h ∈ H, ∀ g, φ (h * g) = φ g)
    (hm : Measurable φ) : ∫⁻ x, lift H φ hφ x ∂(Measure.map (mk H) ν) = ∫⁻ g, φ g ∂ν := by
  rw [lintegral_map (measurable_lift H hφ hm) (measurable_mk H)]
  rfl

/-- Restriction of the pushforward measure to a measurable set of `H \ A`. -/
theorem restrict_map_mk (ν : Measure A) {s : Set (Space H)} (hs : MeasurableSet s) :
    (Measure.map (mk H) ν).restrict s = Measure.map (mk H) (ν.restrict (mk H ⁻¹' s)) :=
  (Measure.restrict_map (measurable_mk H) hs)

/-- `Lᵖ` seminorms of descended measurable functions against the pushforward measure. -/
theorem eLpNorm_lift {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ν : Measure A) (p : ℝ≥0∞) {f : A → E}
    (hf : ∀ h ∈ H, ∀ g, f (h * g) = f g) (hm : Measurable f) :
    eLpNorm (lift H f hf) p (Measure.map (mk H) ν) = eLpNorm f p ν := by
  rw [eLpNorm_map_measure (measurable_lift H hf hm).aestronglyMeasurable
    (measurable_mk H).aemeasurable]
  rfl

/-- Membership in `Lᵖ` of descended measurable functions. -/
theorem memLp_lift_iff {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ν : Measure A) (p : ℝ≥0∞) {f : A → E}
    (hf : ∀ h ∈ H, ∀ g, f (h * g) = f g) (hm : Measurable f) :
    MemLp (lift H f hf) p (Measure.map (mk H) ν) ↔ MemLp f p ν := by
  rw [memLp_map_measure_iff (measurable_lift H hf hm).aestronglyMeasurable
    (measurable_mk H).aemeasurable]
  rfl

/-- Left translation by a point normalizing `H` descends to `H \ A`. -/
def shift (a : A) (ha : ∀ h ∈ H, a * h * a⁻¹ ∈ H) : Space H → Space H :=
  Quotient.map (a * ·) fun x y hxy => by
    have hyx : y * x⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hxy
    refine QuotientGroup.rightRel_apply.mpr ?_
    have := ha _ hyx
    simpa only [mul_inv_rev, mul_assoc] using this

@[simp] theorem shift_mk (a : A) (ha : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (g : A) :
    shift H a ha (mk H g) = mk H (a * g) := rfl

theorem measurable_shift [MeasurableMul A] (a : A) (ha : ∀ h ∈ H, a * h * a⁻¹ ∈ H) :
    Measurable (shift H a ha) :=
  measurable_of_comp H ((measurable_mk H).comp (measurable_const_mul a))

/-- A set of `A` is a union of cosets `H g`. -/
def IsInvariantSet (B : Set A) : Prop := ∀ h ∈ H, ∀ g, h * g ∈ B ↔ g ∈ B

theorem isInvariantSet_preimage_mk (s : Set (Space H)) : IsInvariantSet H (mk H ⁻¹' s) := by
  intro h hh g
  simp only [mem_preimage, mk_mul H hh]

/-- Scaling of the pushforward measure under the descended translation. -/
theorem map_shift_map_mk [MeasurableMul A] (ν : Measure A) (a : A)
    (ha : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (k : ℝ≥0∞)
    (hν : ∀ B : Set A, MeasurableSet B → IsInvariantSet H B → ν ((a * ·) ⁻¹' B) = k * ν B) :
    Measure.map (shift H a ha) (Measure.map (mk H) ν) = k • Measure.map (mk H) ν := by
  ext s hs
  rw [Measure.map_apply (measurable_shift H a ha) hs, Measure.smul_apply,
    Measure.map_apply (measurable_mk H) ((measurable_shift H a ha) hs),
    Measure.map_apply (measurable_mk H) hs, smul_eq_mul]
  have hpre : mk H ⁻¹' (shift H a ha ⁻¹' s) = (a * ·) ⁻¹' (mk H ⁻¹' s) := by
    ext g
    simp only [mem_preimage, shift_mk]
  rw [hpre]
  exact hν _ hs (isInvariantSet_preimage_mk H s)

/-- The renormalizing shift on `H \ A` from an `H`-invariant height increased by one under
left translation by `a`, with measure scaling `c²`. -/
def renormalizingShift [MeasurableMul A] (ν : Measure A) (a : A)
    (ha : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (c : ℝ≥0) (hc : 0 < c)
    (hν : ∀ B : Set A, MeasurableSet B → IsInvariantSet H B →
      ν ((a * ·) ⁻¹' B) = ((c ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * ν B)
    (ht : A → ℝ) (htm : Measurable ht) (htH : ∀ h ∈ H, ∀ g, ht (h * g) = ht g)
    (hta : ∀ g, ht (a * g) = ht g + 1) :
    L2RenormalizingShift (Measure.map (mk H) ν) where
  shift := shift H a ha
  measurable_shift := measurable_shift H a ha
  height := lift H ht htH
  measurable_height := measurable_lift H htH htm
  height_shift := by
    intro x
    induction x using Quotient.inductionOn with
    | h g => exact hta g
  factor := c
  factor_pos := hc
  map_shift := by
    rw [map_shift_map_mk H ν a ha _ hν]
    rfl

end Langlands.Analysis.CosetSpaceShift
