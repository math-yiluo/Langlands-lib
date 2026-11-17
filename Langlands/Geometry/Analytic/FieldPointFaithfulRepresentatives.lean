import Langlands.Geometry.Analytic.FieldPointFaithfulFactorization
import Langlands.Geometry.Analytic.GlobalChartSourceMaps

/-! # Faithful local representatives of arbitrary full field points -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open Set CategoryTheory PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]

namespace AffinoidAtlasPresentation.FieldPoint

/-- On any containing chart, equality of bounded evaluations determines
both the point and all its other chart evaluations. -/
theorem eq_of_boundedEval_eq
    {A : AffinoidAtlasPresentation.{u, v, w} K}
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p q : FieldPoint L A) (i : A.atlas.Index)
    (hp : p.point ∈ range (A.atlas.chart i))
    (hq : q.point ∈ range (A.atlas.chart i))
    (he : p.boundedEval i hp = q.boundedEval i hq) : p = q := by
  obtain ⟨s, hs, hn⟩ := p.isChartPoint i hp
  obtain ⟨t, ht, hm⟩ := q.isChartPoint i hq
  have hst : s = t := by
    apply BanachSpectrum.ext
    intro a
    exact (hn a).symm.trans ((congrArg norm (congrArg
      (fun c : BoundedAlgHom K (A.atlas.algebra i) L => c a) he)).trans (hm a))
  exact eq_of_eval_eq hd (hs.symm.trans ((congrArg (A.atlas.chart i) hst).trans ht))
    i hp hq (congrArg BoundedAlgHom.toAlgHom he)

end AffinoidAtlasPresentation.FieldPoint

namespace SmallAffinoidSpectrum

variable (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]
  {B : SaturatedAtlasPresentation.{u, v, v} K}

/-- A bounded algebra map into the retained original algebra defines an
actual strong map from the small spectrum into any selected target chart. -/
def chartMap (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R) : saturated.{u, v} R ⟶ B :=
  SaturatedAtlasPresentation.chartSourceMap (globalIndex R) (globalRange R) j
    ((globalAlgebra R).symm ▸ φ)

/-- All points of the small-spectrum map land in the selected target chart. -/
theorem chartMap_admissible (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R)
    (c : (saturated.{u, v} R).presentation.atlas.Index) :
    (chartMap R j φ).baseMap '' range ((saturated R).presentation.atlas.chart c) ⊆
      range (B.presentation.atlas.chart j) :=
  SaturatedAtlasPresentation.chartSourceMap_admissible
    (globalIndex R) (globalRange R) j _ c

/-- The bounded global pullback is the supplied map transported only
along the retained global-algebra equality. -/
theorem chartMap_pullback (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R)
    (h : (chartMap R j φ).baseMap ''
      range ((saturated R).presentation.atlas.chart (globalIndex R)) ⊆
        range (B.presentation.atlas.chart j)) :
    (chartMap R j φ).pullback (globalIndex R) j h = (globalAlgebra R).symm ▸ φ :=
  SaturatedAtlasPresentation.chartSourceMap_pullback_global
    (globalIndex R) (globalRange R) j _ h

omit [CompleteSpace K] [CompleteSpace L] in
private theorem character_comp_transport
    {R' S : PresentedAffinoidAlgebra K} (h : R' = R)
    (χ : BoundedAlgHom K R L) (φ : BoundedAlgHom K S R) :
    (h.symm ▸ χ).comp (h.symm ▸ φ) = χ.comp φ := by
  subst R
  rfl

/-- The chart-source map sends its full character point to any prescribed
full target point with the same bounded chart evaluation. -/
theorem fieldPoint_chartMap
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (χ : BoundedAlgHom K R L) (p : FieldPoint L B.presentation)
    (j : B.presentation.atlas.Index) (hj : p.point ∈ range (B.presentation.atlas.chart j))
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j) R)
    (h : χ.comp φ = p.boundedEval j hj) :
    (fieldPoint R hd χ).map (chartMap R j φ) (saturated R).hasAllLocalDomains = p := by
  have hi := (globalRange R).symm ▸ mem_univ (fieldPoint R hd χ).point
  have hy := chartMap_admissible R j φ (globalIndex R)
    ⟨(fieldPoint R hd χ).point, hi, rfl⟩
  apply FieldPoint.eq_of_boundedEval_eq hd _ p j hy hj
  refine (FieldPoint.map_boundedEval (fieldPoint R hd χ) (chartMap R j φ)
    (saturated R).hasAllLocalDomains j hy (globalIndex R) hi
      (chartMap_admissible R j φ (globalIndex R))).trans ?_
  simp only [fieldPoint, FieldPoint.boundedEval_ofGlobalCharacter, chartMap_pullback]
  exact (character_comp_transport R (globalAlgebra R) χ φ).trans h

end SmallAffinoidSpectrum

namespace AffinoidAtlasPresentation.FieldPoint

open PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {A : SaturatedAtlasPresentation.{u, v, v} K}

/-- Requotient the evaluation on an actual containing chart to obtain a
faithful test source in the original space universe. -/
def chartTestSource (p : FieldPoint L A.presentation) (i : A.presentation.atlas.Index)
    (hi : p.point ∈ range (A.presentation.atlas.chart i)) :
    SaturatedAtlasPresentation.{u, v, v} K :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  testSource (p.boundedEval i hi)

/-- The faithful full point on the local chart-evaluation quotient. -/
def chartTestPoint (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation) (i : A.presentation.atlas.Index)
    (hi : p.point ∈ range (A.presentation.atlas.chart i)) :
    FieldPoint L (p.chartTestSource i hi).presentation :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  testPoint (p.boundedEval i hi) hd

/-- The actual faithful local representative into the original saturated
presentation, defined by the local quotient map. -/
def chartTestMap (p : FieldPoint L A.presentation) (i : A.presentation.atlas.Index)
    (hi : p.point ∈ range (A.presentation.atlas.chart i)) : p.chartTestSource i hi ⟶ A :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  letI := small_spectrum.{u, v} (p.boundedEval i hi)
  SmallAffinoidSpectrum.chartMap (algebra (p.boundedEval i hi)) i
    (PresentedAffinoidAlgebra.FaithfulCharacterQuotient.map (p.boundedEval i hi))

omit [CompleteSpace L] in
/-- Every point of the faithful local representative lies in its selected
actual target chart. -/
theorem chartTestMap_admissible (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (c : (p.chartTestSource i hi).presentation.atlas.Index) :
    (p.chartTestMap i hi).baseMap ''
      range ((p.chartTestSource i hi).presentation.atlas.chart c) ⊆
        range (A.presentation.atlas.chart i) := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  let := small_spectrum.{u, v} (p.boundedEval i hi)
  exact SmallAffinoidSpectrum.chartMap_admissible _ _ _ c

/-- The faithful chart representative maps its full test point to the
original full point, with all chart evaluations and compatibilities. -/
theorem chartTestPoint_map (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation) (i : A.presentation.atlas.Index)
    (hi : p.point ∈ range (A.presentation.atlas.chart i)) :
    (p.chartTestPoint hd i hi).map (p.chartTestMap i hi)
      (p.chartTestSource i hi).hasAllLocalDomains = p := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  let := small_spectrum.{u, v} (p.boundedEval i hi)
  exact SmallAffinoidSpectrum.fieldPoint_chartMap _ hd _ p i hi _
    (character_comp_map (p.boundedEval i hi))

end AffinoidAtlasPresentation.FieldPoint

end Langlands.Analytic
