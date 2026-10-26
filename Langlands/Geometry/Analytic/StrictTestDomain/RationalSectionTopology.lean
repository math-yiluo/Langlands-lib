import Langlands.Geometry.Analytic.StrictTestDomain.RationalSectionContinuityProof
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Isometry

/-! # The quotient-norm topology of an invariant rational section action -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory Filter
open scoped Topology
open PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K} (d : RationalData K P)
  {G : Type v} [Group G] (ρ : G →* locusStabilizer d)

/-- The inverse parameter gives the inverse operator on the actual quotient. -/
@[simp] theorem sectionMap_inv_apply (g : G) (b : d.algebra) :
    stabilizerSectionMap d (ρ g⁻¹) (stabilizerSectionMap d (ρ g) b) = b := by
  change ((stabilizerSectionMap d (ρ g⁻¹)).comp
    (stabilizerSectionMap d (ρ g))) b = b
  rw [← stabilizerSectionMap_mul, ← map_mul, inv_mul_cancel, map_one,
    stabilizerSectionMap_one, BoundedAlgHom.id_apply]

/-- Precisely the parameters preserving every quotient norm form a subgroup. -/
def sectionIsometrySubgroup : Subgroup G where
  carrier := {g | ∀ b : d.algebra, ‖stabilizerSectionMap d (ρ g) b‖ = ‖b‖}
  one_mem' := by
    intro b
    rw [map_one, stabilizerSectionMap_one, BoundedAlgHom.id_apply]
  mul_mem' := by
    intro g h hg hh b
    rw [map_mul, stabilizerSectionMap_mul, BoundedAlgHom.comp_apply, hg, hh]
  inv_mem' := by
    intro g hg b
    have h := hg (stabilizerSectionMap d (ρ g⁻¹) b)
    have hi : stabilizerSectionMap d (ρ g)
        (stabilizerSectionMap d (ρ g⁻¹) b) = b := by
      simpa only [inv_inv] using sectionMap_inv_apply d ρ g⁻¹ b
    rw [hi] at h
    exact h.symm

@[simp] theorem mem_sectionIsometrySubgroup (g : G) :
    g ∈ sectionIsometrySubgroup d ρ ↔
      ∀ b : d.algebra, ‖stabilizerSectionMap d (ρ g) b‖ = ‖b‖ := Iff.rfl

/-- On this subgroup each actual section operator preserves distances. -/
theorem isometry_sectionMap (g : sectionIsometrySubgroup d ρ) :
    Isometry (stabilizerSectionMap d (ρ (g : G))) := by
  apply Isometry.of_dist_eq
  intro b c
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact g.property (b - c)

variable [TopologicalSpace G] [IsTopologicalGroup G]
  (hb : ∀ a : P, Continuous (fun g : G => (ρ g : Aut P).hom.toAlgHom a))

include hb in
/-- Finitely many continuous coordinate orbits give a uniform local contraction
bound for every section of the invariant quotient. -/
theorem eventually_section_contractive :
    ∀ᶠ g in 𝓝 (1 : G), ∀ b : d.algebra,
      ‖stabilizerSectionMap d (ρ g) b‖ ≤ ‖b‖ := by
  apply eventually_contractive_of_coordinates (fun g => stabilizerSectionMap d (ρ g))
  · intro i
    exact (continuous_section_orbit d ρ hb (coordinate K d.algebra i)).continuousAt
  · intro i
    rw [map_one, stabilizerSectionMap_one, BoundedAlgHom.id_apply]
    exact coordinate_norm_le_one d.algebra i

include hb in
/-- Contraction for both a parameter and its inverse forces exact norm
preservation on one common neighborhood of the identity. -/
theorem eventually_section_isometry :
    ∀ᶠ g in 𝓝 (1 : G), g ∈ sectionIsometrySubgroup d ρ := by
  have hi : Tendsto (fun g : G => g⁻¹) (𝓝 (1 : G)) (𝓝 (1 : G)) := by
    simpa only [inv_one] using (continuous_inv.continuousAt (x := (1 : G))).tendsto
  filter_upwards [eventually_section_contractive d ρ hb,
    hi.eventually (eventually_section_contractive d ρ hb)] with g hg hgi
  intro b
  apply le_antisymm (hg b)
  simpa only [sectionMap_inv_apply] using hgi (stabilizerSectionMap d (ρ g) b)

/-- The full subgroup of quotient-norm isometries is open, with openness derived
from continuous base orbits rather than assumed operator bounds. -/
def sectionIsometryOpenSubgroup : OpenSubgroup G where
  toSubgroup := sectionIsometrySubgroup d ρ
  isOpen' := (sectionIsometrySubgroup d ρ).isOpen_of_mem_nhds
    (eventually_section_isometry d ρ hb)

@[simp] theorem mem_sectionIsometryOpenSubgroup (g : G) :
    g ∈ sectionIsometryOpenSubgroup d ρ hb ↔
      ∀ b : d.algebra, ‖stabilizerSectionMap d (ρ g) b‖ = ‖b‖ := Iff.rfl

include hb in
/-- Joint quotient-norm continuity at an identity parameter. -/
theorem continuousAt_section_evaluation_one (b : d.algebra) :
    ContinuousAt (fun p : G × d.algebra =>
      stabilizerSectionMap d (ρ p.1) p.2) (1, b) := by
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have ho : ContinuousAt (fun p : G × d.algebra =>
      stabilizerSectionMap d (ρ p.1) b) (1, b) :=
    (continuous_section_orbit d ρ hb b).continuousAt.comp continuous_fst.continuousAt
  have hc : ContinuousAt (fun p : G × d.algebra => p.2) (1, b) :=
    continuous_snd.continuousAt
  filter_upwards [
    continuous_fst.continuousAt.tendsto.eventually (eventually_section_contractive d ρ hb),
    Metric.continuousAt_iff'.mp ho (ε / 2) hε2,
    Metric.continuousAt_iff'.mp hc (ε / 2) hε2] with p hp hpo hpb
  have hleft : dist (stabilizerSectionMap d (ρ p.1) p.2)
      (stabilizerSectionMap d (ρ p.1) b) ≤ dist p.2 b := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hp (p.2 - b)
  calc
    dist (stabilizerSectionMap d (ρ p.1) p.2)
        (stabilizerSectionMap d (ρ (1 : G)) b) ≤
      dist (stabilizerSectionMap d (ρ p.1) p.2)
        (stabilizerSectionMap d (ρ p.1) b) +
      dist (stabilizerSectionMap d (ρ p.1) b)
        (stabilizerSectionMap d (ρ (1 : G)) b) := dist_triangle _ _ _
    _ < ε := by linarith only [hleft, hpo, hpb]

include hb in
/-- The actual invariant rational-quotient section action is jointly continuous
for the product of the group topology and the quotient norm topology. -/
theorem continuous_section_evaluation :
    Continuous (fun p : G × d.algebra =>
      (stabilizerSectionAction d (ρ p.1)).hom.toAlgHom p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, b⟩
  have ht : Tendsto (fun p : G × d.algebra => (g⁻¹ * p.1, p.2))
      (𝓝 (g, b)) (𝓝 ((1 : G), b)) := by
    have h : ContinuousAt (fun p : G × d.algebra => (g⁻¹ * p.1, p.2)) (g, b) :=
      (continuous_const.mul continuous_fst).continuousAt.prodMk
        continuous_snd.continuousAt
    simpa only [inv_mul_cancel] using h.tendsto
  have h := (stabilizerSectionMap d (ρ g)).continuous.continuousAt.tendsto.comp
    ((continuousAt_section_evaluation_one d ρ hb b).tendsto.comp ht)
  have heq : (fun p : G × d.algebra =>
      stabilizerSectionMap d (ρ g)
        (stabilizerSectionMap d (ρ (g⁻¹ * p.1)) p.2)) =
      (fun p => stabilizerSectionMap d (ρ p.1) p.2) := by
    funext p
    change ((stabilizerSectionMap d (ρ g)).comp
      (stabilizerSectionMap d (ρ (g⁻¹ * p.1)))) p.2 = _
    rw [← stabilizerSectionMap_mul, ← map_mul, mul_inv_cancel_left]
  have hcenter : stabilizerSectionMap d (ρ g)
      (stabilizerSectionMap d (ρ (1 : G)) b) =
      stabilizerSectionMap d (ρ g) b := by
    rw [map_one, stabilizerSectionMap_one, BoundedAlgHom.id_apply]
  change Tendsto (fun p : G × d.algebra =>
    stabilizerSectionMap d (ρ g)
      (stabilizerSectionMap d (ρ (g⁻¹ * p.1)) p.2)) (𝓝 (g, b))
    (𝓝 (stabilizerSectionMap d (ρ g)
      (stabilizerSectionMap d (ρ (1 : G)) b))) at h
  rw [heq, hcenter] at h
  exact h

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
