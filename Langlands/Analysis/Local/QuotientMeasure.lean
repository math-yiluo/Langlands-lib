import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration on a left coset space

Subgroup averaging uses right Haar measure because the quotient consists of
left cosets `H * g`. General existence of a compatible quotient measure is an
explicit proposition. The quotient by the trivial subgroup is constructed.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uG uA

variable {G : Type uG} [Group G]

/-- Left cosets `H * g`, without any normality hypothesis on `H`. -/
abbrev LeftQuotient (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

/-- Descent of an actually left-invariant function. -/
def descend (H : Subgroup G) {A : Sort uA} (f : G → A)
    (hf : ∀ h : H, ∀ g, f (h.val * g) = f g) : LeftQuotient H → A :=
  Quotient.lift f (by
    intro g k hgk
    let h : H := ⟨k * g⁻¹, QuotientGroup.rightRel_apply.mp hgk⟩
    simpa [h, mul_assoc] using (hf h g).symm)

@[simp] theorem descend_mk (H : Subgroup G) {A : Sort uA} (f : G → A)
    (hf : ∀ h : H, ∀ g, f (h.val * g) = f g) (g : G) :
    descend H f hf (Quotient.mk _ g) = f g := rfl

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Right multiplication acts by homeomorphisms on the left coset space. -/
def rightTranslate (H : Subgroup G) (g : G) : LeftQuotient H ≃ₜ LeftQuotient H :=
  Homeomorph.Quotient.congr (Homeomorph.mulRight g) (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ H ↔ (y * g) * (x * g)⁻¹ ∈ H
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left])

@[simp] theorem rightTranslate_mk (H : Subgroup G) (g x : G) :
    rightTranslate H g (Quotient.mk _ x) = Quotient.mk _ (x * g) := rfl

@[simp] theorem rightTranslate_one (H : Subgroup G) (q : LeftQuotient H) :
    rightTranslate H 1 q = q := by
  induction q using Quotient.inductionOn with
  | h x => simp

theorem rightTranslate_mul (H : Subgroup G) (g k : G) (q : LeftQuotient H) :
    rightTranslate H k (rightTranslate H g q) = rightTranslate H (g * k) q := by
  induction q using Quotient.inductionOn with
  | h x => simp [mul_assoc]

/-- There are no identifications in the quotient by the trivial subgroup. -/
def trivialQuotientHomeomorph : LeftQuotient (⊥ : Subgroup G) ≃ₜ G :=
  (Homeomorph.Quotient.congrRight (by
    intro x y
    rw [QuotientGroup.rightRel_apply]
    change (y * x⁻¹ ∈ (⊥ : Subgroup G)) ↔ x = y
    simp only [Subgroup.mem_bot, mul_inv_eq_one]
    exact eq_comm)).trans Homeomorph.quotientBot

omit [IsTopologicalGroup G] in
@[simp] theorem trivialQuotientHomeomorph_mk (x : G) :
    trivialQuotientHomeomorph (Quotient.mk _ x) = x := rfl

omit [IsTopologicalGroup G] in
@[simp] theorem trivialQuotientHomeomorph_symm_apply (x : G) :
    trivialQuotientHomeomorph.symm x = Quotient.mk _ x := rfl

end Topology

section Averaging

variable (H : Subgroup G) [MeasurableSpace H] [MeasurableMul H]
variable (μH : Measure H) [IsMulRightInvariant μH]

/-- The actual orbital integral. Right invariance is what makes it descend to
the left quotient. This is the total Bochner integral, before integrability. -/
def orbitAverage (f : G → ℂ) (g : G) : ℂ :=
  ∫ h : H, f (h.val * g) ∂μH

theorem orbitAverage_left_mul (f : G → ℂ) (h : H) (g : G) :
    orbitAverage H μH f (h.val * g) = orbitAverage H μH f g := by
  simpa only [orbitAverage, Subgroup.coe_mul, mul_assoc] using
    integral_mul_right_eq_self (μ := μH) (fun k : H => f (k.val * g)) h

/-- The orbital integral as a function on the actual left quotient. -/
def quotientAverage (f : G → ℂ) : LeftQuotient H → ℂ :=
  descend H (orbitAverage H μH f) (orbitAverage_left_mul H μH f)

@[simp] theorem quotientAverage_mk (f : G → ℂ) (g : G) :
    quotientAverage H μH f (Quotient.mk _ g) = ∫ h : H, f (h.val * g) ∂μH := rfl

theorem quotientAverage_rightTranslate [TopologicalSpace G] [IsTopologicalGroup G]
    (f : G → ℂ) (g : G) (q : LeftQuotient H) :
    quotientAverage H μH f (rightTranslate H g q) =
      quotientAverage H μH (fun x => f (x * g)) q := by
  induction q using Quotient.inductionOn with
  | h x => simp only [rightTranslate_mk, quotientAverage_mk, mul_assoc]

end Averaging

section Compatible

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
variable [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
variable (μG : Measure G) (μH : Measure H) [IsMulRightInvariant μH]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- A specified quotient measure is compatible when it is nonzero and regular,
is invariant under right translation, and satisfies the Weil integral formula
for compactly supported continuous complex functions, with integrability.

This is a property of actual measures, not an assertion that one exists. -/
structure IsCompatible (ν : Measure (LeftQuotient H)) : Prop where
  nonzero : ν ≠ 0
  regular : ν.Regular
  right_invariant : ∀ g : G, MeasurePreserving (rightTranslate H g) ν ν
  averaging_integrable : ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
    Integrable (quotientAverage H μH f) ν
  integral_formula : ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
    (∫ q, quotientAverage H μH f q ∂ν) = ∫ g, f g ∂μG

/-- The genuine existence obligation for the supplied group and subgroup
measures. No quotient measure is selected from an unproved assertion. -/
def CompatibleMeasureExists : Prop :=
  ∃ ν : Measure (LeftQuotient H), IsCompatible H μG μH ν

end Compatible

section Trivial

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable [MeasurableSpace (LeftQuotient (⊥ : Subgroup G))]
variable [BorelSpace (LeftQuotient (⊥ : Subgroup G))]

/-- Probability Haar measure on the trivial subgroup is right invariant. -/
instance trivialSubgroupDirac_rightInvariant :
    IsMulRightInvariant (Measure.dirac (1 : (⊥ : Subgroup G))) where
  map_mul_right_eq_self h := by
    have hh : h = 1 := Subsingleton.elim _ _
    subst h
    simpa only [mul_one] using
      (Measure.map_id' (μ := Measure.dirac (1 : (⊥ : Subgroup G))))

omit [MeasurableSpace (LeftQuotient (⊥ : Subgroup G))]
  [BorelSpace (LeftQuotient (⊥ : Subgroup G))] in
@[simp] theorem quotientAverage_bot_mk (f : G → ℂ) (g : G) :
    quotientAverage (⊥ : Subgroup G) (Measure.dirac 1) f (Quotient.mk _ g) = f g := by
  rw [quotientAverage_mk]
  have hf : (fun h : (⊥ : Subgroup G) => f (h.val * g)) = fun _ => f g := by
    funext h
    rw [Subgroup.mem_bot.mp h.property, one_mul]
  rw [hf]
  simp

/-- The actual quotient measure for the trivial subgroup, transported along
the canonical homeomorphism. This construction does not generalize to a
noncompact subgroup by taking the same pushforward. -/
def trivialQuotientMeasure (μG : Measure G) :
    Measure (LeftQuotient (⊥ : Subgroup G)) :=
  Measure.map trivialQuotientHomeomorph.symm μG

omit [IsTopologicalGroup G] in
theorem trivialQuotientMeasure_regular (μG : Measure G) [μG.Regular] :
    (trivialQuotientMeasure μG).Regular :=
  Measure.Regular.map trivialQuotientHomeomorph.symm

omit [IsTopologicalGroup G] in
theorem integral_trivialQuotientMeasure (μG : Measure G)
    (f : LeftQuotient (⊥ : Subgroup G) → ℂ) :
    (∫ q, f q ∂trivialQuotientMeasure μG) = ∫ g, f (Quotient.mk _ g) ∂μG :=
  integral_map_equiv trivialQuotientHomeomorph.symm.toMeasurableEquiv f

theorem trivialQuotientMeasure_right_invariant (μG : Measure G)
    [IsMulRightInvariant μG] (g : G) :
    MeasurePreserving (rightTranslate (⊥ : Subgroup G) g)
      (trivialQuotientMeasure μG) (trivialQuotientMeasure μG) := by
  refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
  rw [trivialQuotientMeasure, Measure.map_map (rightTranslate _ g).continuous.measurable
    trivialQuotientHomeomorph.symm.continuous.measurable]
  change Measure.map (fun x : G => Quotient.mk _ (x * g)) μG =
    Measure.map trivialQuotientHomeomorph.symm μG
  change Measure.map (trivialQuotientHomeomorph.symm ∘ fun x : G => x * g) μG = _
  rw [← Measure.map_map trivialQuotientHomeomorph.symm.continuous.measurable
    (measurable_mul_const g), map_mul_right_eq_self]

/-- The trivial-subgroup quotient measure satisfies every compatibility field.
No general quotient-measure existence hypothesis is used. -/
theorem trivialQuotientMeasure_isCompatible (μG : Measure G) [μG.Regular]
    [IsMulRightInvariant μG] (hμG : μG ≠ 0) :
    IsCompatible (⊥ : Subgroup G) μG (Measure.dirac 1) (trivialQuotientMeasure μG) where
  nonzero := (Measure.map_ne_zero_iff
    trivialQuotientHomeomorph.symm.continuous.measurable.aemeasurable).2 hμG
  regular := trivialQuotientMeasure_regular μG
  right_invariant := trivialQuotientMeasure_right_invariant μG
  averaging_integrable f hf hc := by
    apply (integrable_map_equiv trivialQuotientHomeomorph.symm.toMeasurableEquiv _).2
    change Integrable (fun x : G =>
      quotientAverage (⊥ : Subgroup G) (Measure.dirac 1) f (Quotient.mk _ x)) μG
    simpa only [quotientAverage_bot_mk] using hf.integrable_of_hasCompactSupport hc (μ := μG)
  integral_formula f _ _ := by
    rw [integral_trivialQuotientMeasure]
    simp only [quotientAverage_bot_mk]

/-- Actual existence in the trivial-subgroup case, including the unipotent
quotient relevant to rank one once its subgroup is identified with `⊥`. -/
theorem trivial_compatibleMeasureExists (μG : Measure G) [μG.Regular]
    [IsMulRightInvariant μG] (hμG : μG ≠ 0) :
    CompatibleMeasureExists (⊥ : Subgroup G) μG (Measure.dirac 1) :=
  ⟨trivialQuotientMeasure μG, trivialQuotientMeasure_isCompatible μG hμG⟩

end Trivial

end Langlands.QuotientIntegration
