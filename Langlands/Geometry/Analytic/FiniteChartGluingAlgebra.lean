import Langlands.Geometry.Analytic.DisjointAffinoidAtlas
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Actual Banach section algebras for finite charts with represented overlaps -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A finite family of actual original charts whose pairwise intersections
are also represented by actual original charts. No affinoid structure on the
union is part of these data. -/
structure FiniteChartGluingData where
  size : ℕ
  index : Fin size → a.Index
  overlap : Fin size → Fin size → a.Index
  overlap_range : ∀ i j, Set.range (a.chart (overlap i j)) =
    Set.range (a.chart (index i)) ∩ Set.range (a.chart (index j))

namespace FiniteChartGluingData

variable {a} (d : FiniteChartGluingData a)

/-- The literal finite union in the original ambient space. -/
def locus : Set X := ⋃ i, Set.range (a.chart (d.index i))

theorem isCompact_locus : IsCompact d.locus :=
  isCompact_iUnion fun i => isCompact_range (a.isEmbedding_chart (d.index i)).continuous

theorem overlap_subset_left (i j : Fin d.size) :
    Set.range (a.chart (d.overlap i j)) ⊆ Set.range (a.chart (d.index i)) := by
  rw [d.overlap_range]
  exact Set.inter_subset_left

theorem overlap_subset_right (i j : Fin d.size) :
    Set.range (a.chart (d.overlap i j)) ⊆ Set.range (a.chart (d.index j)) := by
  rw [d.overlap_range]
  exact Set.inter_subset_right

/-- The original stored bounded restriction to the actual intersection. -/
def leftRestriction (i j : Fin d.size) :
    BoundedAlgHom K (a.algebra (d.index i)) (a.algebra (d.overlap i j)) :=
  a.restriction _ _ (d.overlap_subset_left i j)

def rightRestriction (i j : Fin d.size) :
    BoundedAlgHom K (a.algebra (d.index j)) (a.algebra (d.overlap i j)) :=
  a.restriction _ _ (d.overlap_subset_right i j)

/-- The actual finite product, with its maximum norm. -/
abbrev Product := ∀ i : Fin d.size, a.algebra (d.index i)

/-- The closed algebra of tuples satisfying the stored bounded overlap
equations. This constructs the section algebra rather than assuming it. -/
def sectionSubalgebra : Subalgebra K d.Product where
  carrier := {s | ∀ i j, d.leftRestriction i j (s i) = d.rightRestriction i j (s j)}
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  one_mem' := by intro i j; simp only [Pi.one_apply, map_one]
  add_mem' := by
    intro s t hs ht i j
    change d.leftRestriction i j (s i + t i) = d.rightRestriction i j (s j + t j)
    rw [map_add, map_add, hs i j, ht i j]
  mul_mem' := by
    intro s t hs ht i j
    change d.leftRestriction i j (s i * t i) = d.rightRestriction i j (s j * t j)
    rw [map_mul, map_mul, hs i j, ht i j]
  algebraMap_mem' := by
    intro c i j
    exact ((d.leftRestriction i j).toAlgHom.commutes c).trans
      ((d.rightRestriction i j).toAlgHom.commutes c).symm

theorem isClosed_sectionSubalgebra : IsClosed (d.sectionSubalgebra : Set d.Product) := by
  change IsClosed {s : d.Product | ∀ i j,
    d.leftRestriction i j (s i) = d.rightRestriction i j (s j)}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((d.leftRestriction i j).continuous.comp (continuous_apply i))
      ((d.rightRestriction i j).continuous.comp (continuous_apply j))

/-- The actual Banach algebra obtained as a closed subalgebra of the finite
product of the original quotient algebras. -/
abbrev SectionAlgebra := d.sectionSubalgebra

instance : CompleteSpace d.SectionAlgebra := d.isClosed_sectionSubalgebra.completeSpace_coe

instance : IsUltrametricDist d.SectionAlgebra := inferInstanceAs
  (IsUltrametricDist {s : d.Product // s ∈ d.sectionSubalgebra})

/-- Each original component is obtained by an actual bounded projection. -/
def projection (i : Fin d.size) :
    BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) where
  toAlgHom := (Pi.evalAlgHom K (fun i => a.algebra (d.index i)) i).comp
    d.sectionSubalgebra.val
  bounded := ⟨1, zero_lt_one, fun s => by
    change ‖s.val i‖ ≤ 1 * ‖s.val‖
    simpa only [one_mul] using norm_le_pi_norm s.val i⟩

@[simp]
theorem projection_apply (i : Fin d.size) (s : d.SectionAlgebra) :
    d.projection i s = s.val i := rfl

theorem projection_overlap (i j : Fin d.size) :
    (d.leftRestriction i j).comp (d.projection i) =
      (d.rightRestriction i j).comp (d.projection j) :=
  BoundedAlgHom.ext fun s => s.property i j

@[ext]
theorem section_ext {s t : d.SectionAlgebra}
    (h : ∀ i, d.projection i s = d.projection i t) : s = t :=
  Subtype.ext (funext h)

variable {S : Type z} [NormedCommRing S] [Algebra K S]

/-- Full bounded-map compatibility on the actual pairwise intersections. -/
def MapCompatible (f : ∀ i : Fin d.size, BoundedAlgHom K S (a.algebra (d.index i))) : Prop :=
  ∀ i j, (d.leftRestriction i j).comp (f i) = (d.rightRestriction i j).comp (f j)

variable (f : ∀ i : Fin d.size, BoundedAlgHom K S (a.algebra (d.index i)))
  (hf : d.MapCompatible f)

/-- The bounded lift is built pointwise into the closed equalizer. A finite
sum of positive component bounds bounds its actual maximum norm. -/
def lift : BoundedAlgHom K S d.SectionAlgebra where
  toAlgHom := (AlgHom.pi fun i => (f i).toAlgHom).codRestrict d.sectionSubalgebra
    (fun s i j => congrArg (fun q : BoundedAlgHom K S (a.algebra (d.overlap i j)) => q s)
      (hf i j))
  bounded := by
    choose M hMpos hM using fun i => (f i).bounded
    have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => (hMpos i).le
    refine ⟨(∑ i, M i) + 1, by linarith, fun s => ?_⟩
    change ‖fun i => f i s‖ ≤ ((∑ i, M i) + 1) * ‖s‖
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg s))).2
    intro i
    have hMi : M i ≤ (∑ j, M j) + 1 := by
      have := Finset.single_le_sum (fun j _ => (hMpos j).le) (Finset.mem_univ i)
      linarith
    exact (hM i s).trans (mul_le_mul_of_nonneg_right hMi (norm_nonneg s))

@[simp]
theorem projection_comp_lift (i : Fin d.size) :
    (d.projection i).comp (d.lift f hf) = f i := rfl

/-- Actual bounded maps into this Banach algebra are detected by all finite
component projections. -/
theorem hom_ext {g h : BoundedAlgHom K S d.SectionAlgebra}
    (hgh : ∀ i, (d.projection i).comp g = (d.projection i).comp h) : g = h := by
  apply BoundedAlgHom.ext
  intro s
  apply d.section_ext
  intro i
  exact congrArg (fun q : BoundedAlgHom K S (a.algebra (d.index i)) => q s) (hgh i)

theorem lift_unique (g : BoundedAlgHom K S d.SectionAlgebra)
    (hg : ∀ i, (d.projection i).comp g = f i) : g = d.lift f hf :=
  d.hom_ext fun i => (hg i).trans (d.projection_comp_lift f hf i).symm

/-- The bounded universal property holds for every normed commutative test
algebra, without completeness, reducedness or a nontrivial valuation. -/
def boundedHomEquiv : BoundedAlgHom K S d.SectionAlgebra ≃
    {f : ∀ i : Fin d.size, BoundedAlgHom K S (a.algebra (d.index i)) //
      d.MapCompatible f} where
  toFun g := ⟨fun i => (d.projection i).comp g, fun i j =>
    congrArg (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.overlap i j)) =>
      q.comp g) (d.projection_overlap i j)⟩
  invFun f := d.lift f.val f.property
  left_inv g := (d.lift_unique _ _ g (fun _ => rfl)).symm
  right_inv _f := Subtype.ext (funext fun _ => rfl)

/-- Each chart maps continuously to the actual spectrum of the Banach
equalizer by its constructed bounded projection. -/
def chartSpectrumMap (i : Fin d.size) :
    C(BanachSpectrum (a.algebra (d.index i)), BanachSpectrum d.SectionAlgebra) :=
  BanachSpectrum.comapContinuous (d.projection i).toBoundedRingHom

/-- The continuous local maps agree on every point of the actual overlap
spectrum, by full algebra compatibility. -/
theorem chartSpectrumMap_overlap (i j : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.overlap i j))) :
    d.chartSpectrumMap i (BanachSpectrum.comap (d.leftRestriction i j).toBoundedRingHom x) =
      d.chartSpectrumMap j
        (BanachSpectrum.comap (d.rightRestriction i j).toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro s
  exact congrArg (fun q : BoundedAlgHom K d.SectionAlgebra
    (a.algebra (d.overlap i j)) => x (q s)) (d.projection_overlap i j)

/-- Agreement is on the literal original ambient overlap, with no
faithfulness-of-points inference for algebra maps. -/
theorem chartSpectrumMap_eq_of_chart_eq (i j : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i)))
    (y : BanachSpectrum (a.algebra (d.index j)))
    (hxy : a.chart (d.index i) x = a.chart (d.index j) y) :
    d.chartSpectrumMap i x = d.chartSpectrumMap j y := by
  have hx : a.chart (d.index i) x ∈ Set.range (a.chart (d.overlap i j)) := by
    rw [d.overlap_range]
    exact ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
  obtain ⟨z, hz⟩ := hx
  have hzx : BanachSpectrum.comap (d.leftRestriction i j).toBoundedRingHom z = x :=
    (a.isEmbedding_chart (d.index i)).injective
      ((a.restriction_chart _ _ _ z).trans hz)
  have hzy : BanachSpectrum.comap (d.rightRestriction i j).toBoundedRingHom z = y :=
    (a.isEmbedding_chart (d.index j)).injective
      ((a.restriction_chart _ _ _ z).trans (hz.trans hxy))
  rw [← hzx, ← hzy]
  exact d.chartSpectrumMap_overlap i j z

end FiniteChartGluingData
end Langlands.Analytic.IndexedAffinoidAtlas
