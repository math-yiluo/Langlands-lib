import Langlands.Geometry.Analytic.FieldPointFaithfulTests
import Langlands.Geometry.Analytic.StrongChartDomainComposition

/-! # Faithful field-point tests in a common target chart -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open Set CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- On a saturated source with a global chart, a bounded pullback from one
common target chart determines the complete strong morphism. -/
theorem eq_of_global_pullback_eq
    (hA : A.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ)
    (f g : StrongHom A B) (j : B.atlas.Index)
    (hf : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hg : g.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (heq : f.pullback i j hf = g.pullback i j hg) : f = g := by
  have hb : f.baseMap = g.baseMap := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hi.symm ▸ mem_univ x
    exact (f.chart_comm i j hf y).symm.trans
      ((congrArg (fun φ => B.atlas.chart j
        (BanachSpectrum.comap φ.toBoundedRingHom y)) heq).trans
          (g.chart_comm i j hg y))
  refine ext_of_saturated hA hb ?_
  intro c
  have hci : range (A.atlas.chart c) ⊆ range (A.atlas.chart i) :=
    hi.symm ▸ subset_univ _
  have hfc := (image_mono hci).trans hf
  refine ⟨j, hfc, ?_⟩
  exact (f.restriction_comp_pullback c i j hci hfc hf).symm.trans
    ((congrArg (fun φ => (A.atlas.restriction c i hci).comp φ) heq).trans
      (g.restriction_comp_pullback c i j hci _ hg))

end AffinoidAtlasPresentation.StrongHom

namespace AffinoidAtlasPresentation.FieldPoint

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- A faithful evaluation on any source chart detects the entire map
restricted to that source chart and a common admissible target chart. -/
theorem restrictChart_eq_of_map_eq
    (p : FieldPoint L A) (hA : A.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (hi : p.point ∈ range (A.atlas.chart i))
    (hinj : Function.Injective (p.eval i hi))
    (f g : StrongHom A B) (j : B.atlas.Index)
    (hf : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hg : g.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (heq : p.map f hA = p.map g hA) :
    f.restrictChart i j hf = g.restrictChart i j hg := by
  apply TopChartPresentation.topPullback_injective
    (A := TopChartPresentation.ofChart A i) (B := TopChartPresentation.ofChart B j)
  exact pullback_eq_of_map_eq p hA i hi hinj f g j hf hg heq

/-- A faithful global evaluation detects maps to arbitrary targets whenever
both images fit inside one common target chart. -/
theorem strongHom_eq_of_common_chart_map_eq
    (p : FieldPoint L A) (hA : A.atlas.HasAllLocalDomains)
    (i : A.atlas.Index) (hi : range (A.atlas.chart i) = univ)
    (hinj : Function.Injective (p.eval i (hi.symm ▸ mem_univ _)))
    (f g : StrongHom A B) (j : B.atlas.Index)
    (hf : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hg : g.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (heq : p.map f hA = p.map g hA) : f = g :=
  StrongHom.eq_of_global_pullback_eq hA i hi f g j hf hg
    (pullback_eq_of_map_eq p hA i _ hinj f g j hf hg heq)

end AffinoidAtlasPresentation.FieldPoint

namespace SmallAffinoidSpectrum

variable [CompleteSpace L]
  (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]

/-- The faithful full point of a small spectrum detects complete strong maps
whose images lie in a common chart of an arbitrary saturated target. -/
theorem hom_eq_of_common_chart_fieldPoint_map_eq
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (χ : BoundedAlgHom K R L) (hχ : Function.Injective χ)
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    (f g : saturated.{u, v} R ⟶ B) (j : B.presentation.atlas.Index)
    (hf : f.baseMap '' range ((saturated R).presentation.atlas.chart (globalIndex R)) ⊆
      range (B.presentation.atlas.chart j))
    (hg : g.baseMap '' range ((saturated R).presentation.atlas.chart (globalIndex R)) ⊆
      range (B.presentation.atlas.chart j))
    (heq : (fieldPoint R hd χ).map f (saturated R).hasAllLocalDomains =
      (fieldPoint R hd χ).map g (saturated R).hasAllLocalDomains) : f = g :=
  AffinoidAtlasPresentation.FieldPoint.strongHom_eq_of_common_chart_map_eq
    _ (saturated R).hasAllLocalDomains (globalIndex R) (globalRange R)
    (fieldPoint_eval_injective R hd χ hχ) f g j hf hg heq

end SmallAffinoidSpectrum

namespace PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {R : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum R)]
  [CompleteSpace L] (χ : BoundedAlgHom K R L)

/-- The kernel-quotient test point detects maps with images in a common
target chart, without a global-chart premise on the target. -/
theorem hom_eq_of_common_chart_testPoint_map_eq
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    {B : SaturatedAtlasPresentation.{u, v, v} K}
    (f g : testSource.{u, v} χ ⟶ B) (j : B.presentation.atlas.Index)
    (hf : ∀ x, f.baseMap x ∈ range (B.presentation.atlas.chart j))
    (hg : ∀ x, g.baseMap x ∈ range (B.presentation.atlas.chart j))
    (heq : (testPoint χ hd).map f (testSource χ).hasAllLocalDomains =
      (testPoint χ hd).map g (testSource χ).hasAllLocalDomains) : f = g := by
  let := small_spectrum.{u, v} χ
  exact SmallAffinoidSpectrum.hom_eq_of_common_chart_fieldPoint_map_eq
    (algebra χ) hd (character χ) (character_injective χ) f g j
    (by rintro _ ⟨x, _, rfl⟩; exact hf x)
    (by rintro _ ⟨x, _, rfl⟩; exact hg x) heq

/-- Sending the quotient test point along a map embeds the family of maps
landing in a fixed chart into the target's actual full field points. -/
def commonChartMapEmbedding
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (B : SaturatedAtlasPresentation.{u, v, v} K) (j : B.presentation.atlas.Index) :
    {f : testSource.{u, v} χ ⟶ B // ∀ x, f.baseMap x ∈ range (B.presentation.atlas.chart j)} ↪
      AffinoidAtlasPresentation.FieldPoint L B.presentation where
  toFun f := (testPoint χ hd).map f.val (testSource χ).hasAllLocalDomains
  inj' := fun f g h => Subtype.ext
    (hom_eq_of_common_chart_testPoint_map_eq χ hd f.val g.val j f.property g.property h)

end PresentedAffinoidAlgebra.FaithfulCharacterQuotient

end Langlands.Analytic
