import Langlands.Geometry.Analytic.FieldPointRepresentativeNaturality

/-! # Restriction and common refinement of faithful local representatives -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint

open Set CategoryTheory PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {A : SaturatedAtlasPresentation.{u, v, v} K}

omit [CompleteSpace L] in
/-- The actual bounded evaluations retain exact compatibility under
restriction between nested containing charts. -/
theorem boundedEval_restriction (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : A.presentation.atlas.Index)
    (hij : range (A.presentation.atlas.chart i) ⊆ range (A.presentation.atlas.chart j)) :
    (p.boundedEval i hi).comp (A.presentation.atlas.restriction i j hij) =
      p.boundedEval j (hij hi) :=
  BoundedAlgHom.ext (AlgHom.congr_fun (p.eval_restriction i j hij hi))

/-- Requotienting the actual restriction gives a map from the smaller
chart's faithful representative to the larger chart's representative. -/
def chartTestRestriction (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : A.presentation.atlas.Index)
    (hij : range (A.presentation.atlas.chart i) ⊆ range (A.presentation.atlas.chart j)) :
    p.chartTestSource i hi ⟶ p.chartTestSource j (hij hi) :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra j)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart j).injective
  testMap (p.boundedEval i hi) (p.boundedEval j (hij hi))
    (A.presentation.atlas.restriction i j hij) (p.boundedEval_restriction i hi j hij)

/-- The restriction map preserves the entire faithful full test point. -/
theorem chartTestPoint_restriction
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : A.presentation.atlas.Index)
    (hij : range (A.presentation.atlas.chart i) ⊆ range (A.presentation.atlas.chart j)) :
    (p.chartTestPoint hd i hi).map (p.chartTestRestriction i hi j hij)
      (p.chartTestSource i hi).hasAllLocalDomains = p.chartTestPoint hd j (hij hi) := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra j)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart j).injective
  exact testPoint_map _ _ _ _ hd

set_option maxHeartbeats 800000 in
/-- Nested-chart restriction commutes with the actual representative
maps as an equality of complete strong morphisms. -/
theorem chartTestRestriction_comp_chartTestMap
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : A.presentation.atlas.Index)
    (hij : range (A.presentation.atlas.chart i) ⊆ range (A.presentation.atlas.chart j)) :
    p.chartTestRestriction i hi j hij ≫ p.chartTestMap j (hij hi) =
      p.chartTestMap i hi := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  apply hom_eq_of_common_chart_testPoint_map_eq (p.boundedEval i hi) hd _ _ j
  · intro x
    exact p.chartTestMap_mem j (hij hi) ((p.chartTestRestriction i hi j hij).baseMap x)
  · intro x
    exact hij (p.chartTestMap_mem i hi x)
  · change (p.chartTestPoint hd i hi).map
        ((p.chartTestRestriction i hi j hij).saturatedComp
          (p.chartTestMap j (hij hi)) _ _) _ =
      (p.chartTestPoint hd i hi).map (p.chartTestMap i hi) _
    rw [map_saturatedComp, chartTestPoint_restriction, chartTestPoint_map,
      chartTestPoint_map]

/-- Any two containing-chart representatives have a common smaller
chart representative, preserving full points and commuting over the target. -/
theorem exists_chartTest_common_refinement
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : A.presentation.atlas.Index) (hj : p.point ∈ range (A.presentation.atlas.chart j)) :
    ∃ (k : A.presentation.atlas.Index) (hk : p.point ∈ range (A.presentation.atlas.chart k))
      (a : p.chartTestSource k hk ⟶ p.chartTestSource i hi)
      (b : p.chartTestSource k hk ⟶ p.chartTestSource j hj),
      (p.chartTestPoint hd k hk).map a (p.chartTestSource k hk).hasAllLocalDomains =
          p.chartTestPoint hd i hi ∧
      (p.chartTestPoint hd k hk).map b (p.chartTestSource k hk).hasAllLocalDomains =
          p.chartTestPoint hd j hj ∧
      a ≫ p.chartTestMap i hi = p.chartTestMap k hk ∧
      b ≫ p.chartTestMap j hj = p.chartTestMap k hk := by
  obtain ⟨k, hsub, hk⟩ := IndexedAffinoidAtlas.exists_chart_inter hi hj
  have hki := hsub.trans inter_subset_left
  have hkj := hsub.trans inter_subset_right
  exact ⟨k, hk, p.chartTestRestriction k hk i hki, p.chartTestRestriction k hk j hkj,
    p.chartTestPoint_restriction hd k hk i hki,
    p.chartTestPoint_restriction hd k hk j hkj,
    p.chartTestRestriction_comp_chartTestMap hd k hk i hki,
    p.chartTestRestriction_comp_chartTestMap hd k hk j hkj⟩

end Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint
