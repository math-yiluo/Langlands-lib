import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic

/-! # Central translates of the conjugates of a coset -/

open scoped Pointwise

namespace Langlands.FiniteRep

variable {G : Type*} [Group G]

/-- The set of products `z * (a⁻¹ * x * a) * u` with `z` central and `u ∈ U`.
For normal `U`, this is the union of the central translates of the conjugates of `xU`. -/
def centralConjugacySaturation (U : Subgroup G) (x : G) : Set G :=
  {g | ∃ (z : Subgroup.center G) (a : G) (u : U),
    g = (z : G) * (a⁻¹ * x * a) * (u : G)}

theorem leftCoset_subset_centralConjugacySaturation (U : Subgroup G) (x : G) :
    x • (U : Set G) ⊆ centralConjugacySaturation U x := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨1, 1, ⟨u, hu⟩, by simp⟩

theorem mem_centralConjugacySaturation_mul_right_iff {U : Subgroup G} {x g u : G}
    (hu : u ∈ U) : g * u ∈ centralConjugacySaturation U x ↔ g ∈ centralConjugacySaturation U x := by
  constructor
  · rintro ⟨z, a, v, hv⟩
    refine ⟨z, a, v * ⟨u⁻¹, U.inv_mem hu⟩, ?_⟩
    change g = (z : G) * (a⁻¹ * x * a) * ((v : G) * u⁻¹)
    rw [← mul_assoc, ← hv, mul_inv_cancel_right]
  · rintro ⟨z, a, v, rfl⟩
    exact ⟨z, a, v * ⟨u, hu⟩, mul_assoc _ _ _⟩

theorem mem_centralConjugacySaturation_mul_left_iff {U : Subgroup G} {x g : G}
    (z : Subgroup.center G) :
    (z : G) * g ∈ centralConjugacySaturation U x ↔ g ∈ centralConjugacySaturation U x := by
  constructor
  · rintro ⟨t, a, u, ht⟩
    refine ⟨z⁻¹ * t, a, u, ?_⟩
    change g = ((z : G)⁻¹ * (t : G)) * (a⁻¹ * x * a) * (u : G)
    rw [mul_assoc (z : G)⁻¹, mul_assoc (z : G)⁻¹, ← ht, inv_mul_cancel_left]
  · rintro ⟨t, a, u, rfl⟩
    exact ⟨z * t, a, u, by simp only [Subgroup.coe_mul, mul_assoc]⟩

private theorem conj_mem_centralConjugacySaturation {U : Subgroup G} [hU : U.Normal]
    {x g : G} (a : G) (hg : g ∈ centralConjugacySaturation U x) :
    a⁻¹ * g * a ∈ centralConjugacySaturation U x := by
  obtain ⟨z, b, v, rfl⟩ := hg
  refine ⟨z, b * a, ⟨a⁻¹ * (v : G) * a, hU.conj_mem' _ v.property a⟩, ?_⟩
  have hz := Subgroup.mem_center_iff.mp z.property a⁻¹
  change a⁻¹ * ((z : G) * (b⁻¹ * x * b) * (v : G)) * a =
    (z : G) * ((b * a)⁻¹ * x * (b * a)) * (a⁻¹ * (v : G) * a)
  rw [mul_assoc (z : G) (b⁻¹ * x * b), ← mul_assoc a⁻¹ (z : G), hz]
  group

theorem mem_centralConjugacySaturation_conj_iff {U : Subgroup G} [U.Normal]
    {x g : G} (a : G) :
    a⁻¹ * g * a ∈ centralConjugacySaturation U x ↔ g ∈ centralConjugacySaturation U x := by
  refine ⟨fun hg => ?_, conj_mem_centralConjugacySaturation a⟩
  simpa [mul_assoc] using conj_mem_centralConjugacySaturation a⁻¹ hg

/-- If `U` is open, a central conjugacy saturation and its complement are unions of open
left cosets of `U`. -/
theorem isClopen_centralConjugacySaturation [TopologicalSpace G] [IsTopologicalGroup G]
    {U : Subgroup G} (hU : IsOpen (U : Set G)) (x : G) :
    IsClopen (centralConjugacySaturation U x) := by
  let S := centralConjugacySaturation U x
  have hcoset (g : G) : IsOpen (g • (U : Set G)) ∧ g ∈ g • (U : Set G) :=
    ⟨hU.smul g, ⟨1, U.one_mem, mul_one g⟩⟩
  refine ⟨⟨isOpen_iff_mem_nhds.mpr fun g hg => ?_⟩, isOpen_iff_mem_nhds.mpr fun g hg => ?_⟩
  · refine Filter.mem_of_superset ((hcoset g).1.mem_nhds (hcoset g).2) ?_
    rintro _ ⟨u, hu, rfl⟩
    exact mt (mem_centralConjugacySaturation_mul_right_iff hu).mp hg
  · refine Filter.mem_of_superset ((hcoset g).1.mem_nhds (hcoset g).2) ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (mem_centralConjugacySaturation_mul_right_iff hu).mpr hg

/-- Truncation to the central conjugacy saturation preserves central covariance. -/
theorem indicator_centralConjugacySaturation_mul_left {U : Subgroup G} {x : G} {f : G → ℂ}
    (ω : Subgroup.center G → ℂ) (hcov : ∀ (z : Subgroup.center G) g, f ((z : G) * g) = ω z * f g)
    (z : Subgroup.center G) (g : G) :
    (centralConjugacySaturation U x).indicator f ((z : G) * g) =
      ω z * (centralConjugacySaturation U x).indicator f g := by
  have hiff := mem_centralConjugacySaturation_mul_left_iff (U := U) (x := x) (g := g) z
  by_cases hg : g ∈ centralConjugacySaturation U x
  · rw [Set.indicator_of_mem (hiff.mpr hg), Set.indicator_of_mem hg, hcov]
  · rw [Set.indicator_of_notMem (mt hiff.mp hg), Set.indicator_of_notMem hg, mul_zero]

/-- Truncation to the central conjugacy saturation at a normal level preserves class
functions. -/
theorem indicator_centralConjugacySaturation_conj {U : Subgroup G} [U.Normal] {x : G} {f : G → ℂ}
    (hconj : ∀ a g, f (a⁻¹ * g * a) = f g) (a g : G) :
    (centralConjugacySaturation U x).indicator f (a⁻¹ * g * a) =
      (centralConjugacySaturation U x).indicator f g := by
  have hiff := mem_centralConjugacySaturation_conj_iff (U := U) (x := x) (g := g) a
  by_cases hg : g ∈ centralConjugacySaturation U x
  · rw [Set.indicator_of_mem (hiff.mpr hg), Set.indicator_of_mem hg, hconj]
  · rw [Set.indicator_of_notMem (mt hiff.mp hg), Set.indicator_of_notMem hg]

/-- At a normal level `U`, truncating a centrally covariant class function constant on `xU`
to the saturation gives a right `U`-invariant function. -/
theorem indicator_centralConjugacySaturation_mul_right {U : Subgroup G} [hU : U.Normal]
    {x : G} {f : G → ℂ} (ω : Subgroup.center G → ℂ)
    (hcov : ∀ (z : Subgroup.center G) g, f ((z : G) * g) = ω z * f g)
    (hconj : ∀ a g, f (a⁻¹ * g * a) = f g)
    (hcoset : ∀ u ∈ U, f (x * u) = f x) (g u : G) (hu : u ∈ U) :
    (centralConjugacySaturation U x).indicator f (g * u) =
      (centralConjugacySaturation U x).indicator f g := by
  let S := centralConjugacySaturation U x
  have hiff := mem_centralConjugacySaturation_mul_right_iff (x := x) (g := g) hu
  by_cases hg : g ∈ S
  · have hvalue (z : Subgroup.center G) (a : G) (v : U) :
        f ((z : G) * (a⁻¹ * x * a) * (v : G)) = ω z * f x := by
      rw [mul_assoc, hcov z, ← hcoset (a * (v : G) * a⁻¹) (hU.conj_mem _ v.property a),
        ← hconj a (x * (a * (v : G) * a⁻¹))]
      congr 1
      group
    rw [Set.indicator_of_mem (hiff.mpr hg), Set.indicator_of_mem hg]
    obtain ⟨z, a, v, rfl⟩ := hg
    rw [mul_assoc _ (v : G) u]
    exact (hvalue z a (v * ⟨u, hu⟩)).trans (hvalue z a v).symm
  · rw [Set.indicator_of_notMem (mt hiff.mp hg), Set.indicator_of_notMem hg]

/-- At an open normal level `U`, truncating a centrally covariant class function constant on
`xU` to the saturation gives a locally constant function. -/
theorem isLocallyConstant_indicator_centralConjugacySaturation [TopologicalSpace G]
    [IsTopologicalGroup G] {U : Subgroup G} [U.Normal] (hU : IsOpen (U : Set G))
    {x : G} {f : G → ℂ} (ω : Subgroup.center G → ℂ)
    (hcov : ∀ (z : Subgroup.center G) g, f ((z : G) * g) = ω z * f g)
    (hconj : ∀ a g, f (a⁻¹ * g * a) = f g)
    (hcoset : ∀ u ∈ U, f (x * u) = f x) :
    IsLocallyConstant ((centralConjugacySaturation U x).indicator f) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨g • (U : Set G), hU.smul g, ⟨1, U.one_mem, mul_one g⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact indicator_centralConjugacySaturation_mul_right ω hcov hconj hcoset g u hu

end Langlands.FiniteRep
