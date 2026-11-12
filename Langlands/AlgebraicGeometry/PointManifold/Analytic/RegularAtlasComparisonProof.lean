import Langlands.AlgebraicGeometry.PointManifold.Analytic.RegularCharts
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Analytic regular-atlas assembly and the intrinsic family criterion: proof -/

noncomputable section

universe u v w z

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

open PointTopology

variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
variable {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] {d : ℕ}

namespace RegularChart

/-- A change of regular charts is `k`-analytic: each coordinate is the quotient of two
inverse-chart regular evaluations, with nonvanishing denominator. -/
theorem contDiffOn_transition (c c' : RegularChart k X d) :
    ContDiffOn k ω (c.homeomorph.symm ≫ₕ c'.homeomorph)
      (c.homeomorph.symm ≫ₕ c'.homeomorph).source := by
  have hsrc : (c.homeomorph.symm ≫ₕ c'.homeomorph).source =
      c.homeomorph.target ∩ c.homeomorph.symm ⁻¹' c'.homeomorph.source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  rw [hsrc]
  refine contDiffOn_pi.2 fun i => ?_
  have hsub : c.homeomorph.target ∩ c.homeomorph.symm ⁻¹' c'.homeomorph.source ⊆
      c.homeomorph.target := inter_subset_left
  have hnum := (c.contDiffOn_inverse_evaluation (c'.numerator i)).mono hsub
  have hden := (c.contDiffOn_inverse_evaluation (c'.denominator i)).mono hsub
  refine (hnum.mul (hden.inv fun v hv => c'.denominator_ne_zero _ hv.2 i)).congr
    fun v hv => ?_
  change c'.homeomorph (c.homeomorph.symm v) i = _
  rw [c'.apply_eq _ hv.2 i, div_eq_mul_inv]
  rfl

end RegularChart

namespace RegularAtlas

/-- The charted space of a regular atlas is a `k`-analytic manifold. -/
theorem isManifold (A : RegularAtlas k X d) :
    letI := A.chartedSpace
    IsManifold 𝓘(k, Fin d → k) ω (RingPoint k X k) := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  rw [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  exact (A.chartAt p).contDiffOn_transition (A.chartAt q)

/-- Every global regular evaluation is `k`-analytic on the atlas charted space. -/
theorem contMDiff_regularEvaluation (A : RegularAtlas k X d)
    (a : AffineCoordinateRing k X) :
    letI := A.chartedSpace
    ContMDiff 𝓘(k, Fin d → k) 𝓘(k, k) ω (fun p : RingPoint k X k => regularEvaluation p a) := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(continuous_regularEvaluation a).continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  change ContDiffAt k ω (fun v => regularEvaluation ((A.chartAt p).homeomorph.symm v) a)
    ((A.chartAt p).homeomorph p)
  exact ((A.chartAt p).contDiffOn_inverse_evaluation a).contDiffAt
    ((A.chartAt p).homeomorph.open_target.mem_nhds
      ((A.chartAt p).homeomorph.map_source (A.mem_source p)))

/-- A family from a `k`-charted space is analytic into the atlas charted space exactly when all
global regular evaluations along it are `k`-analytic. -/
theorem contMDiff_iff_regularAnalytic (A : RegularAtlas k X d)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace k E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners k E H)
    {M : Type z} [TopologicalSpace M] [ChartedSpace H M] (f : M → RingPoint k X k) :
    letI := A.chartedSpace
    ContMDiff I 𝓘(k, Fin d → k) ω f ↔ RegularAnalytic I f := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  refine ⟨fun hf a => (A.contMDiff_regularEvaluation a).comp hf, fun hf => ?_⟩
  have hcont : Continuous f :=
    (continuous_iff_regularEvaluation f).2 fun a => (hf a).continuous
  intro t
  rw [contMDiffAt_iff_target]
  refine ⟨hcont.continuousAt, contMDiffAt_pi_space.2 fun i => ?_⟩
  have hev : ∀ᶠ s in 𝓝 t, f s ∈ (A.chartAt (f t)).homeomorph.source :=
    hcont.continuousAt.preimage_mem_nhds
      ((A.chartAt (f t)).homeomorph.open_source.mem_nhds (A.mem_source (f t)))
  have hdiv : ContDiffAt k ω (fun q : k × k => q.1 * q.2⁻¹)
      (regularEvaluation (f t) ((A.chartAt (f t)).numerator i),
        regularEvaluation (f t) ((A.chartAt (f t)).denominator i)) :=
    contDiffAt_fst.mul
      (contDiffAt_snd.inv ((A.chartAt (f t)).denominator_ne_zero _ (A.mem_source _) i))
  have hquot : ContMDiffAt I 𝓘(k, k) ω
      ((fun q : k × k => q.1 * q.2⁻¹) ∘ fun s =>
        (regularEvaluation (f s) ((A.chartAt (f t)).numerator i),
          regularEvaluation (f s) ((A.chartAt (f t)).denominator i))) t :=
    ContDiffAt.comp_contMDiffAt (x := t) (f := fun s =>
        (regularEvaluation (f s) ((A.chartAt (f t)).numerator i),
          regularEvaluation (f s) ((A.chartAt (f t)).denominator i)))
      hdiv ((hf _ t).prodMk_space (hf _ t))
  refine hquot.congr_of_eventuallyEq ?_
  filter_upwards [hev] with s hs
  change (A.chartAt (f t)).homeomorph (f s) i = _
  rw [(A.chartAt (f t)).apply_eq _ hs i, div_eq_mul_inv]
  rfl

end RegularAtlas

end Langlands.AlgebraicGeometry.PointManifold.Analytic
