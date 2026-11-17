import Langlands.Geometry.Analytic.FieldPointFaithfulRepresentatives
import Langlands.Geometry.Analytic.FieldPointCommonChartTests

/-! # Naturality of faithful local field-point representatives -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint

open Set CategoryTheory PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {A B : SaturatedAtlasPresentation.{u, v, v} K}

omit [CompleteSpace L] in
/-- The entire faithful representative lies in its chosen actual target chart. -/
theorem chartTestMap_mem (p : FieldPoint L A.presentation)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (x : (p.chartTestSource i hi).presentation.space) :
    (p.chartTestMap i hi).baseMap x ∈ range (A.presentation.atlas.chart i) := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  let := small_spectrum.{u, v} (p.boundedEval i hi)
  exact p.chartTestMap_admissible i hi
    (SmallAffinoidSpectrum.globalIndex (algebra (p.boundedEval i hi)))
    ⟨x, (SmallAffinoidSpectrum.globalRange (algebra (p.boundedEval i hi))).symm ▸
      mem_univ x, rfl⟩

/-- An admissible strong-map pullback descends to the quotients of its
actual source and image evaluations, giving a map of faithful representatives. -/
def chartTestTransition (p : FieldPoint L A.presentation) (f : A ⟶ B)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : B.presentation.atlas.Index)
    (hij : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    p.chartTestSource i hi ⟶
      (p.map f A.hasAllLocalDomains).chartTestSource j (hij ⟨p.point, hi, rfl⟩) :=
  letI : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  letI : Small.{v} (BanachSpectrum (B.presentation.atlas.algebra j)) :=
    small_of_injective (B.presentation.atlas.isEmbedding_chart j).injective
  testMap (p.boundedEval i hi)
    ((p.map f A.hasAllLocalDomains).boundedEval j (hij ⟨p.point, hi, rfl⟩))
    (f.pullback i j hij)
    (p.map_boundedEval f A.hasAllLocalDomains j _ i hi hij).symm

/-- The induced map preserves the full faithful test points, including
all chart evaluations and restriction compatibilities. -/
theorem chartTestPoint_transition
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation) (f : A ⟶ B)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : B.presentation.atlas.Index)
    (hij : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    (p.chartTestPoint hd i hi).map (p.chartTestTransition f i hi j hij)
      (p.chartTestSource i hi).hasAllLocalDomains =
        (p.map f A.hasAllLocalDomains).chartTestPoint hd j (hij ⟨p.point, hi, rfl⟩) := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  let : Small.{v} (BanachSpectrum (B.presentation.atlas.algebra j)) :=
    small_of_injective (B.presentation.atlas.isEmbedding_chart j).injective
  exact testPoint_map _ _ _ _ hd

set_option maxHeartbeats 800000 in
/-- The representative square for every admissible strong-map pullback
commutes as an equality of complete strong morphisms. -/
theorem chartTestMap_naturality
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (p : FieldPoint L A.presentation) (f : A ⟶ B)
    (i : A.presentation.atlas.Index) (hi : p.point ∈ range (A.presentation.atlas.chart i))
    (j : B.presentation.atlas.Index)
    (hij : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    p.chartTestMap i hi ≫ f =
      p.chartTestTransition f i hi j hij ≫
        (p.map f A.hasAllLocalDomains).chartTestMap j (hij ⟨p.point, hi, rfl⟩) := by
  let : Small.{v} (BanachSpectrum (A.presentation.atlas.algebra i)) :=
    small_of_injective (A.presentation.atlas.isEmbedding_chart i).injective
  apply hom_eq_of_common_chart_testPoint_map_eq (p.boundedEval i hi) hd _ _ j
  · intro x
    exact hij ⟨(p.chartTestMap i hi).baseMap x, p.chartTestMap_mem i hi x, rfl⟩
  · intro x
    exact (p.map f A.hasAllLocalDomains).chartTestMap_mem j
      (hij ⟨p.point, hi, rfl⟩) ((p.chartTestTransition f i hi j hij).baseMap x)
  · change (p.chartTestPoint hd i hi).map
        ((p.chartTestMap i hi).saturatedComp f _ _) _ =
      (p.chartTestPoint hd i hi).map
        ((p.chartTestTransition f i hi j hij).saturatedComp
          ((p.map f A.hasAllLocalDomains).chartTestMap j _) _ _) _
    rw [map_saturatedComp, map_saturatedComp, chartTestPoint_map,
      chartTestPoint_transition, chartTestPoint_map]

end Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint
