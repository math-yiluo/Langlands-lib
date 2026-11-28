import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Products on the central quotient -/

noncomputable section

namespace Langlands.FiniteRep

open MeasureTheory

variable {G : Type*} [Group G]

private theorem center_mul_eq_of_mk_eq {x y : G}
    (h : (QuotientGroup.mk x : G ⧸ Subgroup.center G) = QuotientGroup.mk y) :
    ∃ z : Subgroup.center G, (z : G) * x = y := by
  let z : Subgroup.center G := ⟨x⁻¹ * y, QuotientGroup.eq.mp h⟩
  refine ⟨z, ?_⟩
  rw [← Subgroup.mem_center_iff.mp z.property x]
  exact mul_inv_cancel_left x y

theorem preimage_mk_image_eq_of_center_invariant {S : Set G}
    (hS : ∀ (z : Subgroup.center G) x, (z : G) * x ∈ S ↔ x ∈ S) :
    (QuotientGroup.mk : G → G ⧸ Subgroup.center G) ⁻¹'
      (QuotientGroup.mk '' S) = S := by
  ext g
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨z, rfl⟩ := center_mul_eq_of_mk_eq h
    exact (hS z x).mpr hx
  · exact fun hg => ⟨g, hg, rfl⟩

/-- The product `f * conj b` descends to the central quotient when both functions
transform by the same unitary scalars under left translation by the centre. -/
def centralCovariantProduct (ω : Subgroup.center G → ℂ) (hu : ∀ z, ‖ω z‖ = 1)
    (f b : G → ℂ) (hf : ∀ (z : Subgroup.center G) g, f (z * g) = ω z * f g)
    (hb : ∀ (z : Subgroup.center G) g, b (z * g) = ω z * b g) :
    G ⧸ Subgroup.center G → ℂ :=
  Quotient.lift (fun g => f g * star (b g)) fun x y h => by
    obtain ⟨z, rfl⟩ := center_mul_eq_of_mk_eq (Quotient.sound h)
    have hz : ω z * star (ω z) = 1 := by
      rw [show star (ω z) = (starRingEnd ℂ) (ω z) from rfl, Complex.mul_conj', hu]
      norm_num
    calc
      f x * star (b x) = (ω z * star (ω z)) * (f x * star (b x)) := by rw [hz, one_mul]
      _ = f ((z : G) * x) * star (b ((z : G) * x)) := by
        rw [hf, hb, star_mul']
        ring

@[simp]
theorem centralCovariantProduct_mk (ω : Subgroup.center G → ℂ) (hu : ∀ z, ‖ω z‖ = 1)
    (f b : G → ℂ) (hf : ∀ (z : Subgroup.center G) g, f (z * g) = ω z * f g)
    (hb : ∀ (z : Subgroup.center G) g, b (z * g) = ω z * b g) (g : G) :
    centralCovariantProduct ω hu f b hf hb (QuotientGroup.mk g) = f g * star (b g) :=
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  {ω : Subgroup.center G → ℂ} {hu : ∀ z, ‖ω z‖ = 1} {f b : G → ℂ}
  {hf : ∀ (z : Subgroup.center G) g, f (z * g) = ω z * f g}
  {hb : ∀ (z : Subgroup.center G) g, b (z * g) = ω z * b g}

/-- A product supported on an open, centrally invariant set is Borel on the central
quotient if both factors are continuous on that set. -/
theorem measurable_centralCovariantProduct {S : Set G} (hS : IsOpen S)
    (hSat : ∀ (z : Subgroup.center G) g, (z : G) * g ∈ S ↔ g ∈ S)
    (hfS : ContinuousOn f S) (hbS : ContinuousOn b S) (hzero : ∀ g ∉ S, f g = 0) :
    Measurable (centralCovariantProduct ω hu f b hf hb) := by
  classical
  let q : G → G ⧸ Subgroup.center G := QuotientGroup.mk
  let p := centralCovariantProduct ω hu f b hf hb
  let U := q '' S
  have hU : IsOpen U := QuotientGroup.isOpenMap_coe _ hS
  have hpre : q ⁻¹' U = S := preimage_mk_image_eq_of_center_invariant hSat
  have hp : ContinuousOn p U := by
    apply ((QuotientGroup.isQuotientMap_mk _).continuousOn_isOpen_iff hU).mpr
    change ContinuousOn (p ∘ q) (q ⁻¹' U)
    rw [hpre]
    exact hfS.mul hbS.star
  have hpU : U.piecewise p (fun _ => 0) = p := by
    funext y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    by_cases hy : q g ∈ U
    · exact Set.piecewise_eq_of_mem U p _ hy
    · have hg : g ∉ S := fun h => hy ⟨g, h, rfl⟩
      change U.piecewise p (fun _ => 0) (q g) = f g * star (b g)
      rw [Set.piecewise_eq_of_notMem U p _ hy, hzero g hg, zero_mul]
  change Measurable p
  rw [← hpU]
  exact hp.measurable_piecewise continuousOn_const hU.measurableSet

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
/-- On a finite measure space, an integrable diagonal product and a bounded second
factor imply integrability of the mixed product. -/
theorem integrable_centralCovariantProduct
    {μ : Measure (G ⧸ Subgroup.center G)} [IsFiniteMeasure μ]
    (hm : Measurable (centralCovariantProduct ω hu f b hf hb))
    (hdiag : Integrable (centralCovariantProduct ω hu f f hf hf) μ)
    {M : ℝ} (hM : ∀ g, ‖b g‖ ≤ M) :
    Integrable (centralCovariantProduct ω hu f b hf hb) μ := by
  refine (((integrable_const (μ := μ) (1 : ℝ)).add hdiag.norm).const_mul M).mono'
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change ‖f g * star (b g)‖ ≤ M * (1 + ‖f g * star (f g)‖)
  rw [norm_mul, norm_star, norm_mul, norm_star]
  calc
    ‖f g‖ * ‖b g‖ ≤ ‖f g‖ * M := mul_le_mul_of_nonneg_left (hM g) (norm_nonneg _)
    _ = M * ‖f g‖ := mul_comm _ _
    _ ≤ M * (1 + ‖f g‖ * ‖f g‖) := by
      apply mul_le_mul_of_nonneg_left _ ((norm_nonneg _).trans (hM g))
      nlinarith [sq_nonneg (‖f g‖ - 1)]

end Langlands.FiniteRep
