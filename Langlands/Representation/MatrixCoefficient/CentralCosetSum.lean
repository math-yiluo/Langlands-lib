import Langlands.Analysis.FiberLIntegral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Integrals over `G ⧸ Z(G)` of functions invariant under an open subgroup

Let `J` be an open subgroup of a topological group `G` containing the center `Z(G)`, and let
`μ` be a left and right invariant Haar measure on `G ⧸ Z(G)`. A function on `G` that is
invariant under right (or left) translation by `J` integrates over `G ⧸ Z(G)` to
`μ (J / Z(G))` times its sum over representatives of the cosets `G ⧸ J`.

* `lintegral_out_eq_mul_tsum`: the right-invariant case, summing over `α.out`.
* `lintegral_out_eq_mul_tsum_inv`: the left-invariant case, summing over `α.out⁻¹`.
* `tsum_out_eq_tsum_out_inv`: for a function invariant on both sides, the two sums agree.
* `lintegral_out_mul_eq`: right translation does not change the integral.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands.CentralCoset

variable {G : Type*} [Group G]

/-- The representative of the class of `g` modulo the center is `g` times a central element. -/
theorem exists_out_mk_eq_mul_center (g : G) :
    ∃ z ∈ Subgroup.center G,
      (QuotientGroup.mk g : G ⧸ Subgroup.center G).out = g * z := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center G) g
  exact ⟨z, z.2, hz⟩

/-- The representative of the class of `g` modulo `J` is `g` times an element of `J`. -/
theorem exists_out_mk_eq_mul (J : Subgroup G) (g : G) :
    ∃ j ∈ J, (QuotientGroup.mk g : G ⧸ J).out = g * j := by
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J g
  exact ⟨j, j.2, hj⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A set stable under right multiplication by an open subgroup is open. -/
theorem isOpen_of_mul_mem (J : Subgroup G) (hJ : IsOpen (J : Set G)) (T : Set G)
    (hT : ∀ g ∈ T, ∀ j ∈ J, g * j ∈ T) : IsOpen T := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun j => g * j) '' (J : Set G), ?_, isOpenMap_mul_left g _ hJ,
    ⟨1, J.one_mem, mul_one g⟩⟩
  rintro _ ⟨j, hj, rfl⟩
  exact hT g hg j hj

/-- A set stable under left multiplication by an open subgroup is open. -/
theorem isOpen_of_mul_mem_left (J : Subgroup G) (hJ : IsOpen (J : Set G)) (T : Set G)
    (hT : ∀ g ∈ T, ∀ j ∈ J, j * g ∈ T) : IsOpen T := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun j => j * g) '' (J : Set G), ?_, isOpenMap_mul_right g _ hJ,
    ⟨1, J.one_mem, one_mul g⟩⟩
  rintro _ ⟨j, hj, rfl⟩
  exact hT g hg j hj

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- For a set stable under right multiplication by the center, the classes whose chosen
representative lies in the set form its image. -/
theorem setOf_out_mem_eq_image (T : Set G)
    (hT : ∀ g ∈ T, ∀ z ∈ Subgroup.center G, g * z ∈ T) :
    {q : G ⧸ Subgroup.center G | q.out ∈ T} = QuotientGroup.mk '' T := by
  ext q
  constructor
  · intro hq
    exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨z, hz, hout⟩ := exists_out_mk_eq_mul_center g
    change (QuotientGroup.mk g : G ⧸ Subgroup.center G).out ∈ T
    rw [hout]
    exact hT g hg z hz

/-- A set of classes defined by an open, center-stable condition on representatives is open. -/
theorem isOpen_setOf_out_mem (T : Set G) (hTo : IsOpen T)
    (hT : ∀ g ∈ T, ∀ z ∈ Subgroup.center G, g * z ∈ T) :
    IsOpen {q : G ⧸ Subgroup.center G | q.out ∈ T} := by
  rw [setOf_out_mem_eq_image T hT]
  exact QuotientGroup.isOpenMap_coe _ hTo

section Measure

variable (J : Subgroup G) (hZJ : Subgroup.center G ≤ J) (hJ : IsOpen (J : Set G))

/-- The image of `J` in `G ⧸ Z(G)`, described through chosen representatives. -/
def centralImage : Set (G ⧸ Subgroup.center G) := {q | q.out ∈ J}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
include hZJ in
theorem mk_mem_centralImage_iff (g : G) :
    (QuotientGroup.mk g : G ⧸ Subgroup.center G) ∈ centralImage J ↔ g ∈ J := by
  obtain ⟨z, hz, hout⟩ := exists_out_mk_eq_mul_center g
  change (QuotientGroup.mk g : G ⧸ Subgroup.center G).out ∈ J ↔ g ∈ J
  rw [hout]
  exact ⟨fun h => by simpa using J.mul_mem h (J.inv_mem (hZJ hz)),
    fun h => J.mul_mem h (hZJ hz)⟩

include hZJ hJ in
theorem isOpen_centralImage : IsOpen (centralImage J) :=
  isOpen_setOf_out_mem (J : Set G) hJ fun _ hg _ hz => J.mul_mem hg (hZJ hz)

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

include hZJ hJ in
/-- A function of the chosen representative that is right `J`-invariant is measurable. -/
theorem measurable_out {M : Type*} [MeasurableSpace M] (Φ : G → M)
    (hΦ : ∀ g, ∀ j ∈ J, Φ (g * j) = Φ g) :
    Measurable fun q : G ⧸ Subgroup.center G => Φ q.out := by
  intro s _
  refine (isOpen_setOf_out_mem (Φ ⁻¹' s) ?_ ?_).measurableSet
  · exact isOpen_of_mul_mem J hJ _ fun g hg j hj => by
      simpa [Set.mem_preimage, hΦ g j hj] using hg
  · intro g hg z hz
    simpa [Set.mem_preimage, hΦ g z (hZJ hz)] using hg

variable (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

omit [BorelSpace (G ⧸ Subgroup.center G)] [μ.IsMulRightInvariant] in
include hZJ hJ in
theorem centralImage_measure_ne_zero : μ (centralImage J) ≠ 0 :=
  (isOpen_centralImage J hZJ hJ).measure_ne_zero μ
    ⟨QuotientGroup.mk 1, (mk_mem_centralImage_iff J hZJ 1).mpr J.one_mem⟩

omit [μ.IsMulRightInvariant] in
include hZJ hJ in
/-- Right `J`-invariant functions: the integral is a sum over the cosets `G ⧸ J`. -/
theorem lintegral_out_eq_mul_tsum (Φ : G → ℝ≥0∞) (hΦ : ∀ g, ∀ j ∈ J, Φ (g * j) = Φ g) :
    ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ =
      μ (centralImage J) * ∑' α : G ⧸ J, Φ α.out := by
  let p : G ⧸ Subgroup.center G → G ⧸ J := fun q => QuotientGroup.mk q.out
  have hp : ∀ q : G ⧸ Subgroup.center G, Φ q.out = (fun α : G ⧸ J => Φ α.out) (p q) := by
    intro q
    obtain ⟨j, hj, hout⟩ := exists_out_mk_eq_mul J q.out
    change Φ q.out = Φ (QuotientGroup.mk q.out : G ⧸ J).out
    rw [hout, hΦ _ j hj]
  have hfib : ∀ α : G ⧸ J, p ⁻¹' {α} =
      (fun q => (QuotientGroup.mk α.out : G ⧸ Subgroup.center G)⁻¹ * q) ⁻¹'
        centralImage J := by
    intro α
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, p]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_centralImage_iff J hZJ]
    conv_lhs => rw [← QuotientGroup.out_eq' α]
    rw [eq_comm, QuotientGroup.eq]
  calc ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ
      = ∫⁻ q, (fun α : G ⧸ J => Φ α.out) (p q) ∂μ := lintegral_congr hp
    _ = μ (centralImage J) * ∑' α : G ⧸ J, Φ α.out := by
      refine Langlands.Analysis.lintegral_comp_eq_mul_tsum μ p _
        (centralImage_measure_ne_zero J hZJ hJ μ) ?_ ?_ (fun α : G ⧸ J => Φ α.out)
      · intro α
        rw [hfib]
        exact (isOpen_centralImage J hZJ hJ).measurableSet.preimage (measurable_const_mul _)
      · intro α
        rw [hfib, measure_preimage_mul]

include hZJ hJ in
/-- Left `J`-invariant functions: the integral is a sum over inverse representatives. -/
theorem lintegral_out_eq_mul_tsum_inv (Φ : G → ℝ≥0∞) (hΦ : ∀ g, ∀ j ∈ J, Φ (j * g) = Φ g) :
    ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ =
      μ (centralImage J) * ∑' α : G ⧸ J, Φ α.out⁻¹ := by
  let p : G ⧸ Subgroup.center G → G ⧸ J := fun q => QuotientGroup.mk q.out⁻¹
  have hp : ∀ q : G ⧸ Subgroup.center G, Φ q.out = (fun α : G ⧸ J => Φ α.out⁻¹) (p q) := by
    intro q
    obtain ⟨j, hj, hout⟩ := exists_out_mk_eq_mul J q.out⁻¹
    change Φ q.out = Φ (QuotientGroup.mk q.out⁻¹ : G ⧸ J).out⁻¹
    rw [hout, mul_inv_rev, inv_inv, hΦ _ _ (J.inv_mem hj)]
  have hfib : ∀ α : G ⧸ J, p ⁻¹' {α} =
      (fun q => q * (QuotientGroup.mk α.out : G ⧸ Subgroup.center G)) ⁻¹'
        centralImage J := by
    intro α
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, p]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [← QuotientGroup.mk_mul, mk_mem_centralImage_iff J hZJ]
    conv_lhs => rw [← QuotientGroup.out_eq' α]
    rw [eq_comm, QuotientGroup.eq]
    constructor
    · intro h
      simpa [mul_inv_rev] using J.inv_mem h
    · intro h
      simpa [mul_inv_rev] using J.inv_mem h
  calc ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ
      = ∫⁻ q, (fun α : G ⧸ J => Φ α.out⁻¹) (p q) ∂μ := lintegral_congr hp
    _ = μ (centralImage J) * ∑' α : G ⧸ J, Φ α.out⁻¹ := by
      refine Langlands.Analysis.lintegral_comp_eq_mul_tsum μ p _
        (centralImage_measure_ne_zero J hZJ hJ μ) ?_ ?_ (fun α : G ⧸ J => Φ α.out⁻¹)
      · intro α
        rw [hfib]
        exact (isOpen_centralImage J hZJ hJ).measurableSet.preimage (measurable_mul_const _)
      · intro α
        rw [hfib, measure_preimage_mul_right]

include hZJ hJ in
/-- For a function invariant under `J` on both sides, the sums over representatives and over
their inverses agree. This is where both invariances of `μ` (unimodularity) are used. -/
theorem tsum_out_eq_tsum_out_inv (hfin : μ (centralImage J) ≠ ∞) (Φ : G → ℝ≥0∞)
    (hΦr : ∀ g, ∀ j ∈ J, Φ (g * j) = Φ g) (hΦl : ∀ g, ∀ j ∈ J, Φ (j * g) = Φ g) :
    ∑' α : G ⧸ J, Φ α.out = ∑' α : G ⧸ J, Φ α.out⁻¹ := by
  have h1 := lintegral_out_eq_mul_tsum J hZJ hJ μ Φ hΦr
  have h2 := lintegral_out_eq_mul_tsum_inv J hZJ hJ μ Φ hΦl
  rw [h1] at h2
  exact (ENNReal.mul_right_inj (centralImage_measure_ne_zero J hZJ hJ μ) hfin).mp h2

omit [μ.IsHaarMeasure] in
/-- Right translation does not change the integral of a function of the chosen
representative that is invariant under the center. -/
theorem lintegral_out_mul_eq (Φ : G → ℝ≥0∞)
    (hΦ : ∀ g, ∀ z ∈ Subgroup.center G, Φ (g * z) = Φ g) (h : G) :
    ∫⁻ q : G ⧸ Subgroup.center G, Φ (q.out * h) ∂μ =
      ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ := by
  have hq : ∀ q : G ⧸ Subgroup.center G,
      Φ (q.out * h) = (fun q' : G ⧸ Subgroup.center G => Φ q'.out)
        (q * (QuotientGroup.mk h : G ⧸ Subgroup.center G)) := by
    intro q
    obtain ⟨z, hz, hout⟩ := exists_out_mk_eq_mul_center (q.out * h)
    change Φ (q.out * h) = Φ (q * (QuotientGroup.mk h : G ⧸ Subgroup.center G)).out
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [← QuotientGroup.mk_mul, hout, hΦ _ z hz]
  calc ∫⁻ q : G ⧸ Subgroup.center G, Φ (q.out * h) ∂μ
      = ∫⁻ q, (fun q' : G ⧸ Subgroup.center G => Φ q'.out)
          (q * (QuotientGroup.mk h : G ⧸ Subgroup.center G)) ∂μ := lintegral_congr hq
    _ = ∫⁻ q : G ⧸ Subgroup.center G, Φ q.out ∂μ :=
      lintegral_mul_right_eq_self (fun q' : G ⧸ Subgroup.center G => Φ q'.out) _

end Measure

end Langlands.CentralCoset
