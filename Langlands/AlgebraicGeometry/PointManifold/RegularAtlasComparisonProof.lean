import Langlands.AlgebraicGeometry.PointManifold.RegularAtlasComparison
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Regular-atlas assembly and the intrinsic family criterion: proof -/

noncomputable section

universe v w z

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold

open PointTopology

variable {k : Type} [RCLike k]
variable {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] {d : ℕ}

namespace RegularChart

/-- A change of regular charts is real `C∞`: each coordinate is the quotient of two
inverse-chart regular evaluations, with nonvanishing denominator. -/
theorem contDiffOn_transition (c c' : RegularChart k X d) :
    ContDiffOn ℝ ∞ (c.homeomorph.symm ≫ₕ c'.homeomorph)
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

/-- The charted space of a regular atlas is a real `C∞` manifold. -/
theorem isManifold (A : RegularAtlas k X d) :
    letI := A.chartedSpace
    IsManifold 𝓘(ℝ, Fin d → k) ∞ (RingPoint k X k) := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  rw [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.id_comp, Function.comp_id]
  exact (A.chartAt p).contDiffOn_transition (A.chartAt q)

/-- Every global regular evaluation is real `C∞` on the atlas charted space. -/
theorem contMDiff_regularEvaluation (A : RegularAtlas k X d)
    (a : AffineCoordinateRing k X) :
    letI := A.chartedSpace
    ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, k) ∞ (fun p : RingPoint k X k => regularEvaluation p a) := by
  let _ : ChartedSpace (Fin d → k) (RingPoint k X k) := A.chartedSpace
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(continuous_regularEvaluation a).continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  change ContDiffAt ℝ ∞ (fun v => regularEvaluation ((A.chartAt p).homeomorph.symm v) a)
    ((A.chartAt p).homeomorph p)
  exact ((A.chartAt p).contDiffOn_inverse_evaluation a).contDiffAt
    ((A.chartAt p).homeomorph.open_target.mem_nhds
      ((A.chartAt p).homeomorph.map_source (A.mem_source p)))

/-- A family from a real charted space is `C∞` into the atlas charted space exactly when all
global regular evaluations along it are real `C∞`. -/
theorem contMDiff_iff_regularSmooth (A : RegularAtlas k X d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (f : M → RingPoint k X k) :
    letI := A.chartedSpace
    ContMDiff I 𝓘(ℝ, Fin d → k) ∞ f ↔ RegularSmooth I f := by
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
  have hdiv : ContDiffAt ℝ ∞ (fun q : k × k => q.1 * q.2⁻¹)
      (regularEvaluation (f t) ((A.chartAt (f t)).numerator i),
        regularEvaluation (f t) ((A.chartAt (f t)).denominator i)) :=
    contDiffAt_fst.mul
      (contDiffAt_snd.inv ((A.chartAt (f t)).denominator_ne_zero _ (A.mem_source _) i))
  have hquot : ContMDiffAt I 𝓘(ℝ, k) ∞
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

/-- Both regular-atlas obligations: smooth assembly of the atlas and the intrinsic family
criterion, for all source universes. -/
theorem regularAtlasComparison (k : Type) [RCLike k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ) :
    regularAtlasComparisonStatement.{v, w, z} k X d := by
  refine ⟨fun A => A.isManifold, ?_⟩
  intro A E _ _ H _ I M _ _ _ f
  exact A.contMDiff_iff_regularSmooth I f

end Langlands.AlgebraicGeometry.PointManifold
