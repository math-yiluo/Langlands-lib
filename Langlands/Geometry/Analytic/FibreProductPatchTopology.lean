import Langlands.Geometry.Analytic.SaturatedAtlasOpenSubspaces
import Langlands.Geometry.Analytic.FibreProductAtlas

/-! # Hausdorff patches in the fibre-product gluing -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- The original pair-chart system restricted to two factor patches. -/
def patchSystem (U : Set A.space) (V : Set B.space) : AffinoidChartSystem.{u, w} K :=
  (chartSystem f g).subsystem (patchPairs f g U V) (isDownwardClosed_patchPairs f g U V)

/-- The comparison to the unrestricted quotient. -/
def patchMap (U : Set A.space) (V : Set B.space) :
    (patchSystem f g U V).Space → (chartSystem f g).Space :=
  (chartSystem f g).subsystemMap (patchPairs f g U V) (isDownwardClosed_patchPairs f g U V)

@[simp]
theorem patchMap_chart (U : Set A.space) (V : Set B.space)
    (p : (patchSystem f g U V).Index) (t : BanachSpectrum (algebra f g p.val)) :
    patchMap f g U V ((patchSystem f g U V).chart p t) =
      (chartSystem f g).chart p.val t := rfl

set_option maxHeartbeats 800000 in
/-- Finite overlaps are local to Hausdorff factor patches. -/
theorem hasFiniteOverlaps_patchSystem (U : Set A.space) (V : Set B.space)
    [T2Space U] [T2Space V] : (patchSystem f g U V).HasFiniteOverlaps := by
  intro p q
  obtain ⟨S₁, hS₁, hS₁sub, hS₁cov⟩ :=
    A.atlas.exists_finite_charts_inter_of_subset_t2Space
      p.val.val.1 q.val.val.1 p.property.1 q.property.1
  obtain ⟨S₂, hS₂, hS₂sub, hS₂cov⟩ :=
    B.atlas.exists_finite_charts_inter_of_subset_t2Space
      p.val.val.2 q.val.val.2 p.property.2 q.property.2
  let P := patchSystem f g U V
  let Q := chartSystem f g
  have hinj : Function.Injective
      (fun k : {k : P.Index // P.Sub k p ∧ P.Sub k q} => k.val.val.val) :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  refine ⟨{k | k.val.val.val.1 ∈ S₁ ∧ k.val.val.val.2 ∈ S₂},
    ((hS₁.prod hS₂).preimage hinj.injOn).subset fun k hk => hk, ?_⟩
  intro s t hst
  have hcpqP : P.chart p s = P.chart q t := P.chart_eq_iff.mpr hst
  have hcpq : Q.chart p.val s = Q.chart q.val t :=
    congrArg (patchMap f g U V) hcpqP
  have hx₁ : A.atlas.chart p.val.val.1 (leftPoint f g p.val s) ∈
      range (A.atlas.chart p.val.val.1) ∩ range (A.atlas.chart q.val.val.1) :=
    ⟨⟨_, rfl⟩, ⟨_, (congrArg (fst f g) hcpq).symm⟩⟩
  have hx₂ : B.atlas.chart p.val.val.2 (rightPoint f g p.val s) ∈
      range (B.atlas.chart p.val.val.2) ∩ range (B.atlas.chart q.val.val.2) :=
    ⟨⟨_, rfl⟩, ⟨_, (congrArg (snd f g) hcpq).symm⟩⟩
  obtain ⟨m₁, hm₁S, hm₁⟩ := mem_iUnion₂.1 (hS₁cov hx₁)
  obtain ⟨m₂, hm₂S, hm₂⟩ := mem_iUnion₂.1 (hS₂cov hx₂)
  let m : PairIndex f g := ⟨(m₁, m₂), base f g p.val,
    ⟨(image_mono ((hS₁sub m₁ hm₁S).trans inter_subset_left)).trans
        (isCommonBase_base f g p.val).1,
      (image_mono ((hS₂sub m₂ hm₂S).trans inter_subset_left)).trans
        (isCommonBase_base f g p.val).2⟩⟩
  have hsubp : Sub f g m p.val :=
    ⟨(hS₁sub m₁ hm₁S).trans inter_subset_left, (hS₂sub m₂ hm₂S).trans inter_subset_left⟩
  have hsubq : Sub f g m q.val :=
    ⟨(hS₁sub m₁ hm₁S).trans inter_subset_right, (hS₂sub m₂ hm₂S).trans inter_subset_right⟩
  let r : P.Index := ⟨m, isDownwardClosed_patchPairs f g U V hsubp p.property⟩
  have hrp : P.Sub r p := hsubp
  have hrq : P.Sub r q := hsubq
  obtain ⟨v', hv'⟩ := (mem_range_restriction_iff f g m p.val hsubp s).mpr ⟨hm₁, hm₂⟩
  refine ⟨⟨r, hrp, hrq⟩, ⟨hm₁S, hm₂S⟩, v', hv', ?_⟩
  apply P.chart_injective q
  have h1 : P.chart q (P.pull hrq v') = P.chart r v' := P.chart_pull hrq v'
  have h2 : P.chart p (P.pull hrp v') = P.chart r v' := P.chart_pull hrp v'
  have h3 : P.pull hrp v' = s := hv'
  rw [h3] at h2
  exact h1.trans (h2.symm.trans hcpqP)

/-- Charts in the patch quotient are closed embeddings. -/
theorem isClosedEmbedding_patchChart (U : Set A.space) (V : Set B.space)
    [T2Space U] [T2Space V] (p : (patchSystem f g U V).Index) :
    IsClosedEmbedding ((patchSystem f g U V).chart p) :=
  (patchSystem f g U V).isClosedEmbedding_chart (hasFiniteOverlaps_patchSystem f g U V) p

end Langlands.Analytic.FibreProduct
