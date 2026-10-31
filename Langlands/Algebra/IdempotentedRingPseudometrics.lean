import Langlands.Algebra.IdempotentedRingUniformity
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The source zero–one pseudometrics

Renard I.1.3, printed p.8/PDF14. Each pseudodistance tests equality
of one actual right coordinate. Their uniformities recover the actual
right-annihilator uniformity.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Filter Set
open scoped Uniformity Topology

universe uA

variable {A : Type uA} [NonUnitalRing A]

namespace Idempotent

/-- The source's zero–one pseudodistance at the actual right coordinate `e`. -/
def rightPseudoDistance (e : Idempotent A) (a b : A) : ℝ :=
  by
    classical
    exact if a * (e : A) = b * (e : A) then 0 else 1

@[simp] theorem rightPseudoDistance_self (e : Idempotent A) (a : A) :
    e.rightPseudoDistance a a = 0 := by
  simp [rightPseudoDistance]

theorem rightPseudoDistance_zero_or_one (e : Idempotent A) (a b : A) :
    e.rightPseudoDistance a b = 0 ∨ e.rightPseudoDistance a b = 1 := by
  classical
  unfold rightPseudoDistance
  split_ifs <;> simp

@[simp] theorem rightPseudoDistance_eq_zero_iff (e : Idempotent A) (a b : A) :
    e.rightPseudoDistance a b = 0 ↔ a * (e : A) = b * (e : A) := by
  simp [rightPseudoDistance]

theorem rightPseudoDistance_eq_zero_iff_sub_mul (e : Idempotent A) (a b : A) :
    e.rightPseudoDistance a b = 0 ↔ (a - b) * (e : A) = 0 := by
  rw [rightPseudoDistance_eq_zero_iff, sub_mul, sub_eq_zero]

theorem rightPseudoDistance_eq_zero_iff_annihilator (e : Idempotent A) (a b : A) :
    e.rightPseudoDistance a b = 0 ↔ a - b ∈ e.rightAnnihilator := by
  simp only [rightPseudoDistance_eq_zero_iff, mem_rightAnnihilator, sub_mul, sub_eq_zero]

@[simp] theorem rightPseudoDistance_lt_one_iff (e : Idempotent A) (a b : A) :
    e.rightPseudoDistance a b < 1 ↔ a * (e : A) = b * (e : A) := by
  classical
  unfold rightPseudoDistance
  split_ifs <;> simp_all

theorem rightPseudoDistance_comm (e : Idempotent A) (a b : A) :
    e.rightPseudoDistance a b = e.rightPseudoDistance b a := by
  classical
  unfold rightPseudoDistance
  simp only [eq_comm]

theorem rightPseudoDistance_triangle (e : Idempotent A) (a b c : A) :
    e.rightPseudoDistance a c ≤ e.rightPseudoDistance a b + e.rightPseudoDistance b c := by
  classical
  by_cases hab : a * (e : A) = b * (e : A) <;>
    by_cases hbc : b * (e : A) = c * (e : A) <;>
    by_cases hac : a * (e : A) = c * (e : A) <;>
    simp_all [rightPseudoDistance]

/-- The actual pseudometric structure for one source pseudodistance.
Install locally; different idempotents give different structures. -/
@[instance_reducible]
def rightPseudoMetricSpace (e : Idempotent A) : PseudoMetricSpace A where
  dist := e.rightPseudoDistance
  dist_self := rightPseudoDistance_self e
  dist_comm := rightPseudoDistance_comm e
  dist_triangle := rightPseudoDistance_triangle e

@[simp] theorem rightPseudoMetricSpace_dist (e : Idempotent A) (a b : A) :
    @dist A e.rightPseudoMetricSpace.toDist a b = e.rightPseudoDistance a b := rfl

theorem rightPseudoDistance_mono {e f : Idempotent A} (hef : e ≤ f) (a b : A) :
    e.rightPseudoDistance a b ≤ f.rightPseudoDistance a b := by
  classical
  by_cases hf : a * (f : A) = b * (f : A)
  · have he : a * (e : A) = b * (e : A) :=
      rightCoordinateEntourage_antitone hef
        (show (a, b) ∈ f.rightCoordinateEntourage from hf)
    simp [rightPseudoDistance, hf, he]
  · simp only [rightPseudoDistance, ite_eq_right hf]
    split_ifs <;> simp

/-- The family of pseudodistances is monotone for the corner order and the
pointwise order on functions. -/
theorem rightPseudoDistance_monotone :
    Monotone (rightPseudoDistance (A := A)) :=
  fun _ _ hef a b => rightPseudoDistance_mono hef a b

/-- One zero–one pseudometric has exactly the principal coordinate uniformity. -/
theorem rightPseudoMetricSpace_uniformity (e : Idempotent A) :
    𝓤[e.rightPseudoMetricSpace.toUniformSpace] = 𝓟 e.rightCoordinateEntourage := by
  let := e.rightPseudoMetricSpace
  apply Filter.ext
  intro s
  rw [Metric.uniformity_basis_dist.mem_iff, Filter.mem_principal]
  constructor
  · rintro ⟨ε, hε, hs⟩ p hp
    apply hs
    change e.rightPseudoDistance p.1 p.2 < ε
    have hp' : p.1 * (e : A) = p.2 * (e : A) := hp
    simp only [rightPseudoDistance, ite_eq_left hp']
    exact hε
  · intro hs
    refine ⟨1, zero_lt_one, ?_⟩
    intro p hp
    apply hs
    exact (rightPseudoDistance_lt_one_iff e p.1 p.2).1 hp

end Idempotent

namespace IsIdempotented

/-- A common upper idempotent dominates both actual pseudodistances pointwise. -/
theorem rightPseudoDistance_common_upper_bound (hA : IsIdempotented A)
    (e f : Idempotent A) :
    ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      (∀ a b : A, e.rightPseudoDistance a b ≤ g.rightPseudoDistance a b) ∧
      (∀ a b : A, f.rightPseudoDistance a b ≤ g.rightPseudoDistance a b) := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have he : e ≤ g := hg e (by simp)
  have hf : f ≤ g := hg f (by simp)
  exact ⟨g, he, hf, Idempotent.rightPseudoDistance_mono he,
    Idempotent.rightPseudoDistance_mono hf⟩

theorem rightPseudoDistance_directed (hA : IsIdempotented A) :
    Directed (· ≤ ·) (Idempotent.rightPseudoDistance (A := A)) := by
  intro e f
  obtain ⟨g, _, _, he, hf⟩ := hA.rightPseudoDistance_common_upper_bound e f
  exact ⟨g, he, hf⟩

end IsIdempotented

/-- The source family generates exactly the actual right-coordinate uniform space. -/
theorem idempotentedRing_iInf_pseudometric_uniformSpace :
    (⨅ e : Idempotent A, e.rightPseudoMetricSpace.toUniformSpace) =
      idempotentedRingUniformSpace A := by
  apply UniformSpace.ext
  rw [iInf_uniformity, idempotentedRing_uniformity]
  congr 1
  funext e
  exact e.rightPseudoMetricSpace_uniformity

/-- Consequently the induced topology is exactly the source annihilator topology. -/
theorem idempotentedRing_iInf_pseudometric_topology :
    (⨅ e : Idempotent A, e.rightPseudoMetricSpace.toUniformSpace).toTopologicalSpace =
      (idempotentedRingUniformSpace A).toTopologicalSpace := by
  rw [idempotentedRing_iInf_pseudometric_uniformSpace]

/-- Equivalently, the infimum of the individual pseudometric topologies is the
source annihilator topology. -/
theorem idempotentedRing_iInf_pseudometric_topologies :
    (⨅ e : Idempotent A, e.rightPseudoMetricSpace.toUniformSpace.toTopologicalSpace) =
      (idempotentedRingUniformSpace A).toTopologicalSpace := by
  rw [← UniformSpace.toTopologicalSpace_iInf,
    idempotentedRing_iInf_pseudometric_uniformSpace]

/-! Complete unapplied interfaces at the arbitrary ring universe. -/

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A → A → A → ℝ :=
  @Idempotent.rightPseudoDistance.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) → (a b : A) →
    (e.rightPseudoDistance a b = 0 ↔ a - b ∈ e.rightAnnihilator) :=
  @Idempotent.rightPseudoDistance_eq_zero_iff_annihilator.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) → (a b : A) →
    (e.rightPseudoDistance a b = 0 ∨ e.rightPseudoDistance a b = 1) :=
  @Idempotent.rightPseudoDistance_zero_or_one.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) → (a b : A) →
    @dist A e.rightPseudoMetricSpace.toDist a b = e.rightPseudoDistance a b :=
  @Idempotent.rightPseudoMetricSpace_dist.{uA}

example : {A : Type uA} → [NonUnitalRing A] → {e f : Idempotent A} → e ≤ f →
    (a b : A) → e.rightPseudoDistance a b ≤ f.rightPseudoDistance a b :=
  @Idempotent.rightPseudoDistance_mono.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (e f : Idempotent A) → ∃ g : Idempotent A, e ≤ g ∧ f ≤ g ∧
      (∀ a b : A, e.rightPseudoDistance a b ≤ g.rightPseudoDistance a b) ∧
      (∀ a b : A, f.rightPseudoDistance a b ≤ g.rightPseudoDistance a b) :=
  @IsIdempotented.rightPseudoDistance_common_upper_bound.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    (⨅ e : Idempotent A, e.rightPseudoMetricSpace.toUniformSpace.toTopologicalSpace) =
      (idempotentedRingUniformSpace A).toTopologicalSpace :=
  @idempotentedRing_iInf_pseudometric_topologies.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    letI : DecidableEq A := Classical.typeDecidableEq A
    ∀ (e : Idempotent A) (a b : A), e.rightPseudoDistance a b =
      (if a * (e : A) = b * (e : A) then (0 : ℝ) else 1) := by
  intro A _
  classical
  intro e a b
  rfl

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A → PseudoMetricSpace A :=
  @Idempotent.rightPseudoMetricSpace.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    𝓤[e.rightPseudoMetricSpace.toUniformSpace] = 𝓟 e.rightCoordinateEntourage :=
  @Idempotent.rightPseudoMetricSpace_uniformity.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    Directed (· ≤ ·) (Idempotent.rightPseudoDistance (A := A)) :=
  @IsIdempotented.rightPseudoDistance_directed.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    (⨅ e : Idempotent A, e.rightPseudoMetricSpace.toUniformSpace) =
      idempotentedRingUniformSpace A :=
  @idempotentedRing_iInf_pseudometric_uniformSpace.{uA}

example : {A : Type uA} → [NonUnitalRing A] →
    (⨅ e : Idempotent A, e.rightPseudoMetricSpace.toUniformSpace).toTopologicalSpace =
      (idempotentedRingUniformSpace A).toTopologicalSpace :=
  @idempotentedRing_iInf_pseudometric_topology.{uA}

end Langlands.Algebra
