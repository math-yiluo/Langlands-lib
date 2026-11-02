import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Homeomorph.Quotient

/-! Shared existing left-coset carriers, translations and topology. -/

noncomputable section

namespace Langlands.Induction

universe uG

variable {G : Type uG} [Group G]

/-- The quotient whose points are right cosets `P * g`, with the quotient topology. -/
abbrev LeftQuotient (P : Subgroup G) := Quotient (QuotientGroup.rightRel P)

/-- The projection to `P \ G`. -/
def quotientMap (P : Subgroup G) (g : G) : LeftQuotient P :=
  Quotient.mk _ g

/-- Right multiplication on `P \ G`. -/
def quotientRight (P : Subgroup G) (g : G) : LeftQuotient P → LeftQuotient P :=
  Quotient.map' (fun x => x * g) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_inv_rev, mul_assoc] using h)

end Langlands.Induction

namespace Langlands.QuotientIntegration

universe uG uA

variable {G : Type uG} [Group G]

/-- Left cosets `H * g`, without any normality hypothesis on `H`. -/
abbrev LeftQuotient (H : Subgroup G) := Langlands.Induction.LeftQuotient H

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

end Topology

/-- The existing canonical projection from the group onto its left cosets. -/
abbrev leftQuotientMap (H : Subgroup G) (g : G) : LeftQuotient H :=
  Langlands.Induction.quotientMap H g

@[simp] theorem leftQuotientMap_apply (H : Subgroup G) (g : G) :
    leftQuotientMap H g = Quotient.mk (QuotientGroup.rightRel H) g := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The projection to left cosets is an open quotient map. -/
theorem leftQuotient_isOpenQuotientMap (H : Subgroup G) :
    IsOpenQuotientMap (leftQuotientMap H) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- Left cosets of a closed subgroup form a Hausdorff space. -/
theorem leftQuotient_t2Space (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    T2Space (LeftQuotient H) := by
  let : IsClosed (H : Set G) := hH
  exact t2Space_quotient_mulAction_of_properSMul

/-- The left quotient of a locally compact group is locally compact. -/
theorem leftQuotient_locallyCompactSpace [LocallyCompactSpace G] (H : Subgroup G) :
    LocallyCompactSpace (LeftQuotient H) :=
  (leftQuotient_isOpenQuotientMap H).locallyCompactSpace

end Langlands.QuotientIntegration
