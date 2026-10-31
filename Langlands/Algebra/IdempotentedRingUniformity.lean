import Langlands.Algebra.IdempotentedRing
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Order.Filter.Bases.Basic

/-!
# Right-annihilator uniformity of an idempotented ring

The uniformity is constructed from the actual right coordinates `a ↦ a * e`.
Its singleton-idempotent basis is Renard I.1.3, printed p.8/PDF14.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Filter Set
open scoped Uniformity Topology

universe u

variable {A : Type u} [NonUnitalRing A]

namespace Idempotent

/-- The source's `A(1-e)`, formed without adjoining a unit. -/
def rightAnnihilator (e : Idempotent A) : AddSubgroup A where
  carrier := {a | a * (e : A) = 0}
  zero_mem' := zero_mul _
  add_mem' := by
    intro a b ha hb
    change (a + b) * (e : A) = 0
    rw [add_mul, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    change (-a) * (e : A) = 0
    rw [neg_mul, ha, neg_zero]

@[simp] theorem mem_rightAnnihilator (e : Idempotent A) (a : A) :
    a ∈ e.rightAnnihilator ↔ a * (e : A) = 0 := Iff.rfl

/-- Annihilators are precisely the images of the residual projections. -/
theorem mem_rightAnnihilator_iff_residual (e : Idempotent A) (a : A) :
    a ∈ e.rightAnnihilator ↔ ∃ b : A, a = b - b * (e : A) := by
  constructor
  · intro ha
    exact ⟨a, by rw [(mem_rightAnnihilator e a).1 ha, sub_zero]⟩
  · rintro ⟨b, rfl⟩
    change (b - b * (e : A)) * e = 0
    rw [sub_mul, mul_assoc, e.property.eq, sub_self]

/-- These additive subgroups are stable under ambient left multiplication. -/
theorem mul_mem_rightAnnihilator (e : Idempotent A) (b : A) {a : A}
    (ha : a ∈ e.rightAnnihilator) : b * a ∈ e.rightAnnihilator := by
  change (b * a) * (e : A) = 0
  rw [mul_assoc, (mem_rightAnnihilator e a).1 ha, mul_zero]

theorem rightAnnihilator_antitone :
    Antitone (rightAnnihilator (A := A)) := by
  intro e f hef a ha
  change a * (e : A) = 0
  have hfe := ((le_iff_mul e f).1 hef).1
  calc
    a * (e : A) = a * ((f : A) * e) := by rw [hfe]
    _ = (a * (f : A)) * e := (mul_assoc _ _ _).symm
    _ = 0 := by rw [(mem_rightAnnihilator f a).1 ha, zero_mul]

/-- Equality of the actual right coordinates is an entourage. -/
def rightCoordinateEntourage (e : Idempotent A) : Set (A × A) :=
  {p | p.1 * (e : A) = p.2 * (e : A)}

@[simp] theorem mem_rightCoordinateEntourage (e : Idempotent A) (a b : A) :
    (a, b) ∈ e.rightCoordinateEntourage ↔ a * (e : A) = b * (e : A) := Iff.rfl

theorem rightCoordinateEntourage_antitone :
    Antitone (rightCoordinateEntourage (A := A)) := by
  intro e f hef p hp
  change p.1 * (e : A) = p.2 * (e : A)
  have hfe := ((le_iff_mul e f).1 hef).1
  have hh := congrArg (fun a : A => a * (e : A)) hp
  simpa only [mul_assoc, hfe] using hh

theorem rightCoordinateEntourage_eq_annihilator (e : Idempotent A) :
    e.rightCoordinateEntourage = {p : A × A | p.1 - p.2 ∈ e.rightAnnihilator} := by
  ext p
  simp only [rightCoordinateEntourage, mem_ofPred_eq, mem_rightAnnihilator,
    sub_mul, sub_eq_zero]

end Idempotent

namespace IsIdempotented

/-- A common upper idempotent refines two actual annihilator subgroups. -/
theorem rightAnnihilator_common_refinement (hA : IsIdempotented A)
    (e f : Idempotent A) :
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      g.rightAnnihilator ≤ e.rightAnnihilator ⊓ f.rightAnnihilator := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have he : e ≤ g := hg e (by simp)
  have hf : f ≤ g := hg f (by simp)
  exact ⟨g, he, hf, le_inf
    (Idempotent.rightAnnihilator_antitone he)
    (Idempotent.rightAnnihilator_antitone hf)⟩

theorem rightCoordinateEntourage_directed (hA : IsIdempotented A) :
    Directed (· ≥ ·) (Idempotent.rightCoordinateEntourage (A := A)) := by
  intro e f
  obtain ⟨g, he, hf, _⟩ := hA.rightAnnihilator_common_refinement e f
  exact ⟨g, Idempotent.rightCoordinateEntourage_antitone he,
    Idempotent.rightCoordinateEntourage_antitone hf⟩

end IsIdempotented

/-- The actual infimum of discrete right-coordinate pullback uniformities.
Install this definition locally; it is deliberately not a global instance. -/
@[instance_reducible]
def idempotentedRingUniformSpace (A : Type u) [NonUnitalRing A] : UniformSpace A :=
  ⨅ e : Idempotent A,
    UniformSpace.comap (fun a : A => a * (e : A)) (⊥ : UniformSpace A)

theorem idempotentedRing_uniformity :
    𝓤[idempotentedRingUniformSpace A] =
      ⨅ e : Idempotent A, 𝓟 e.rightCoordinateEntourage := by
  rw [idempotentedRingUniformSpace, iInf_uniformity]
  congr 1
  funext e
  rw [uniformity_comap, bot_uniformity, comap_principal]
  rfl

theorem idempotentedRing_uniformity_hasBasis (hA : IsIdempotented A) :
    (𝓤[idempotentedRingUniformSpace A]).HasBasis (fun _ : Idempotent A => True)
      Idempotent.rightCoordinateEntourage := by
  let : Nonempty (Idempotent A) := ⟨⟨0, IsIdempotentElem.zero⟩⟩
  rw [idempotentedRing_uniformity]
  exact hasBasis_iInf_principal hA.rightCoordinateEntourage_directed

theorem idempotentedRing_nhds_hasBasis (hA : IsIdempotented A) (b : A) :
    let := idempotentedRingUniformSpace A
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {a : A | (a - b) * (e : A) = 0}) := by
  let := idempotentedRingUniformSpace A
  have h := nhds_basis_uniformity (idempotentedRing_uniformity_hasBasis hA) (x := b)
  simpa only [Idempotent.rightCoordinateEntourage, mem_ofPred_eq,
    sub_mul, sub_eq_zero] using h

theorem idempotentedRing_nhds_zero_hasBasis (hA : IsIdempotented A) :
    let := idempotentedRingUniformSpace A
    (𝓝 (0 : A)).HasBasis (fun _ : Idempotent A => True)
      (fun e => (e.rightAnnihilator : Set A)) := by
  let := idempotentedRingUniformSpace A
  change (𝓝 (0 : A)).HasBasis (fun _ : Idempotent A => True)
    (fun e => {a : A | a * (e : A) = 0})
  simpa only [sub_zero] using
    idempotentedRing_nhds_hasBasis hA (0 : A)

theorem idempotentedRing_uniformContinuous_rightCoordinate (e : Idempotent A) :
    @UniformContinuous A A (idempotentedRingUniformSpace A) (⊥ : UniformSpace A)
      (fun a : A => a * (e : A)) := by
  rw [uniformContinuous_iff_le_comap]
  exact iInf_le _ e

/-! Complete unapplied interfaces on the actual given ring. -/

example : (A : Type u) → [NonUnitalRing A] → UniformSpace A :=
  idempotentedRingUniformSpace.{u}

example : {A : Type u} → [NonUnitalRing A] → IsIdempotented A →
    (𝓤[idempotentedRingUniformSpace A]).HasBasis (fun _ : Idempotent A => True)
      Idempotent.rightCoordinateEntourage :=
  @idempotentedRing_uniformity_hasBasis.{u}

example : {A : Type u} → [NonUnitalRing A] → IsIdempotented A → (b : A) →
    let := idempotentedRingUniformSpace A
    (𝓝 b).HasBasis (fun _ : Idempotent A => True)
      (fun e => {a : A | (a - b) * (e : A) = 0}) :=
  @idempotentedRing_nhds_hasBasis.{u}

example : {A : Type u} → [NonUnitalRing A] → IsIdempotented A →
    let := idempotentedRingUniformSpace A
    (𝓝 (0 : A)).HasBasis (fun _ : Idempotent A => True)
      (fun e => (e.rightAnnihilator : Set A)) :=
  @idempotentedRing_nhds_zero_hasBasis.{u}

example : {A : Type u} → [NonUnitalRing A] → (e : Idempotent A) →
    @UniformContinuous A A (idempotentedRingUniformSpace A) (⊥ : UniformSpace A)
      (fun a : A => a * (e : A)) :=
  @idempotentedRing_uniformContinuous_rightCoordinate.{u}

end Langlands.Algebra
