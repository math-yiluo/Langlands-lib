import Langlands.Analysis.Local.QuotientTopology
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Bases

/-!
# Measurability and s-finiteness support for quotient fiber kernels
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal Topology Uniformity

universe u v

/-- Normalize every fiber by one plus its total mass. -/
def massNormalizedKernel {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y) : Kernel X Y :=
  ⟨fun x => (κ x univ + 1)⁻¹ • κ x, by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun x => (κ x univ + 1)⁻¹ * κ x s)
    exact measurable_mul.comp
      (((κ.measurable_coe MeasurableSet.univ).add measurable_const).inv.prodMk
        (κ.measurable_coe hs))⟩

/-- A pointwise finite measurable kernel is s-finite, even when its total
masses have no common finite bound. -/
theorem kernel_isSFinite_of_finite_mass {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y)
    (hκ : ∀ x, κ x univ ≠ ⊤) : IsSFiniteKernel κ := by
  let d : X → ℝ≥0∞ := fun x => κ x univ + 1
  have hd : Measurable d := (κ.measurable_coe MeasurableSet.univ).add measurable_const
  have hd0 (x) : d x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_left le_rfl))
  have hdt (x) : d x ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hκ x, ENNReal.one_ne_top⟩
  let η : Kernel X Y := massNormalizedKernel κ
  have hη : IsFiniteKernel η := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun x => ?_⟩⟩
    change (d x)⁻¹ * κ x univ ≤ 1
    calc
      _ ≤ (d x)⁻¹ * d x := by
        gcongr
        exact le_add_right le_rfl
      _ = 1 := ENNReal.inv_mul_cancel (hd0 x) (hdt x)
  have heq : η.withDensity (fun x _ => d x) = κ := by
    ext x : 1
    rw [Kernel.withDensity_apply η (f := fun x _ => d x)
      (show Measurable (Function.uncurry (fun (x : X) (_ : Y) => d x)) from
        hd.comp measurable_fst)]
    change ((d x)⁻¹ • κ x).withDensity (fun _ => d x) = κ x
    rw [withDensity_const, smul_smul, ENNReal.mul_inv_cancel (hd0 x) (hdt x), one_smul]
  rw [← heq]
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel η (fun x _ => hdt x)

/-- A single countable measurable cover on which every fiber measure is
finite suffices for s-finiteness of a measurable kernel. -/
theorem kernel_isSFinite_of_finite_cover {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y)
    (s : ℕ → Set Y) (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) (hfinite : ∀ x n, κ x (s n) ≠ ⊤) :
    IsSFiniteKernel κ := by
  let sd := disjointed s
  have hsd : ∀ n, MeasurableSet (sd n) := MeasurableSet.disjointed hs
  have hrestr (n) : IsSFiniteKernel (κ.restrict (hsd n)) := by
    apply kernel_isSFinite_of_finite_mass
    intro x
    rw [Kernel.restrict_apply' _ _ _ MeasurableSet.univ, univ_inter]
    exact ne_top_of_le_ne_top (hfinite x n) (measure_mono (disjointed_subset s n))
  have heq : κ = Kernel.sum (fun n => κ.restrict (hsd n)) := by
    ext x : 1
    change κ x = Measure.sum (fun n => (κ x).restrict (sd n))
    rw [← Measure.restrict_iUnion (disjoint_disjointed s) hsd,
      iUnion_disjointed, hcover, Measure.restrict_univ]
  rw [heq]
  exact Kernel.isSFiniteKernel_sum_of_denumerable hrestr

/-- Compact finiteness of every fiber on a sigma-compact Hausdorff target
implies s-finiteness of a measurable kernel. -/
theorem kernel_isSFinite_of_compact_finite {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
    [BorelSpace Y] [T2Space Y] [SigmaCompactSpace Y] (κ : Kernel X Y)
    (hκ : ∀ x (K : Set Y), IsCompact K → κ x K ≠ ⊤) : IsSFiniteKernel κ := by
  apply kernel_isSFinite_of_finite_cover κ (compactCovering Y)
    (fun n => (isCompact_compactCovering Y n).measurableSet) (iUnion_compactCovering Y)
  exact fun x n => hκ x _ (isCompact_compactCovering Y n)

/-- A locally compact second countable Hausdorff group is Polish in its
existing topology. The complete right uniformity supplies a compatible
complete metric. -/
theorem polishSpace_of_locallyCompact_group (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] : PolishSpace G := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : IsRightUniformGroup G := ⟨rfl⟩
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have : (𝓤 G).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one']
    infer_instance
  let : MetrizableSpace G := UniformSpace.metrizableSpace
  infer_instance

/-- A function on the actual left quotient is measurable precisely when its
pullback to a locally compact second countable group is measurable. -/
theorem measurable_quotient_iff {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    {Y : Type v} [MeasurableSpace Y] (f : LeftQuotient H → Y) :
    Measurable f ↔ Measurable (f ∘ leftQuotientMap H) := by
  let := leftQuotient_t2Space H hH
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  let : PolishSpace G := polishSpace_of_locallyCompact_group G
  exact (continuous_quotient_mk'.measurable.measurable_comp_iff_of_surjective
    (leftQuotient_isOpenQuotientMap H).surjective).symm

end Langlands.QuotientIntegration
