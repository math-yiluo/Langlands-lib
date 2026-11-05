import Langlands.Geometry.Analytic.StrongRefiningSourceSeparation
import Langlands.Geometry.Analytic.SaturatedDomainHomPresheaf
import Langlands.Geometry.Analytic.SaturatedLiteralDomainGluing

/-! # Whole-chart strong representatives of actual quotient arrows -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set AffinoidAtlasPresentation
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- If every contained original chart of a domain is selected, its entire
original presentation maps into the selected ambient atlas. -/
def selectedDomainFactor (P : A.presentation.atlas.RefiningSelection)
    (S : A.presentation.atlas.OriginalChartDomain)
    (hS : ∀ c : A.presentation.atlas.SubspaceChart S.carrier, c.val ∈ P) :
    A.originalDomain S ⟶ A.refiningSubpresentation P where
  baseMap := (A.originalDomainInclusion S).baseMap
  target_exists c := ⟨⟨c.val, hS c⟩, by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩⟩
  pullback c j h := (A.originalDomainInclusion S).pullback c j.val h
  chart_comm c j h x := (A.originalDomainInclusion S).chart_comm c j.val h x
  restriction_comm c c' j j' hc hj h h' :=
    (A.originalDomainInclusion S).restriction_comm c c' j.val j'.val hc hj h h'

/-- The factorization triangle is equality of all complete strong-map data. -/
theorem selectedDomainFactor_comp_inclusion
    (P : A.presentation.atlas.RefiningSelection)
    (S : A.presentation.atlas.OriginalChartDomain)
    (hS : ∀ c : A.presentation.atlas.SubspaceChart S.carrier, c.val ∈ P) :
    selectedDomainFactor P S hS ≫ A.refiningSubatlasInclusion P =
      A.originalDomainInclusion S := by
  refine StrongHom.ext_of_saturated (A.originalDomain S).hasAllLocalDomains rfl ?_
  intro c
  let j : (A.refiningSubpresentation P).presentation.atlas.Index := ⟨c.val, hS c⟩
  have hf : (selectedDomainFactor P S hS).baseMap ''
      Set.range ((A.originalDomain S).presentation.atlas.chart c) ⊆
        Set.range ((A.refiningSubpresentation P).presentation.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hg : (A.refiningSubatlasInclusion P).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart j) ⊆
        Set.range (A.presentation.atlas.chart c.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcomp := (selectedDomainFactor P S hS).comp_admissible
    (A.refiningSubatlasInclusion P) c j c.val hf hg
  refine ⟨c.val, hcomp, ?_⟩
  refine (StrongHom.saturatedComp_pullback (selectedDomainFactor P S hS)
    (A.refiningSubatlasInclusion P) (A.originalDomain S).hasAllLocalDomains
    (A.refiningSubpresentation P).hasAllLocalDomains c j c.val hf hg hcomp).trans ?_
  change (A.presentation.atlas.restriction c.val c.val _).comp
      (A.presentation.atlas.restriction c.val c.val _) =
    A.presentation.atlas.restriction c.val c.val _
  simp only [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- A selected original chart has every contained original chart selected,
so it admits the actual full strong factor into the selected atlas. -/
def selectedChartFactor (P : A.presentation.atlas.RefiningSelection)
    (i : A.presentation.atlas.Index) (hi : i ∈ P) :
    A.originalDomain (ofChart i) ⟶ A.refiningSubpresentation P :=
  selectedDomainFactor P (ofChart i)
    (fun c => P.downward_closed c.val i c.property hi)

/-- Precomposition of a strong domain map is the direct full restriction. -/
theorem originalDomainStrongMap_comp_eq_restrictOriginalDomain
    {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T)
    (f : A.originalDomain T ⟶ B) :
    ((A.presentation.originalDomainStrongMap hST :
        A.originalDomain S ⟶ A.originalDomain T) ≫ f : A.originalDomain S ⟶ B) =
      StrongHom.restrictOriginalDomain (A := A.presentation) (B := B.presentation)
        f hST := by
  refine StrongHom.ext_of_saturated (A.originalDomain S).hasAllLocalDomains rfl ?_
  intro c
  let d : A.presentation.atlas.SubspaceChart T.carrier :=
    ⟨c.val, c.property.trans hST⟩
  obtain ⟨j, hj⟩ := f.target_exists d
  have hc : (A.presentation.originalDomainStrongMap hST).baseMap ''
      Set.range ((A.originalDomain S).presentation.atlas.chart c) ⊆
        Set.range ((A.originalDomain T).presentation.atlas.chart d) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hcomp := (A.presentation.originalDomainStrongMap hST).comp_admissible f
    c d j hc hj
  refine ⟨j, hcomp, ?_⟩
  refine (StrongHom.saturatedComp_pullback
    (A.presentation.originalDomainStrongMap hST) f
    (A.originalDomain S).hasAllLocalDomains (A.originalDomain T).hasAllLocalDomains
    c d j hc hj hcomp).trans ?_
  change (A.presentation.atlas.restriction c.val c.val _).comp
    (f.pullback d j hj) = f.pullback d j _
  erw [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

namespace SourceCategory

/-- The constructed quotient domain inclusion is the image of the full
original bounded-map inclusion between the same domain presentations. -/
theorem domainMap_eq_strongFunctor
    {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T) :
    domainMap hST = strongFunctor.map
      (A.presentation.originalDomainStrongMap hST :
        A.originalDomain S ⟶ A.originalDomain T) := by
  apply (cancel_mono (domainInclusion A T)).1
  erw [domainMap_inclusion, ← Functor.map_comp,
    originalDomainStrongMap_comp_eq_restrictOriginalDomain]
  rfl

/-- Actual quotient restriction of a literal strong map agrees with its
direct full strong restriction, including every bounded pullback. -/
theorem domainMap_comp_strong
    {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T)
    (f : A.originalDomain T ⟶ B) :
    domainMap hST ≫ strongFunctor.map f =
      strongFunctor.map (f.restrictOriginalDomain hST) := by
  erw [domainMap_eq_strongFunctor, ← Functor.map_comp,
    originalDomainStrongMap_comp_eq_restrictOriginalDomain]

/-- The entire numerator restricts strongly to any domain whose original
contained charts are selected. Its quotient class is the prescribed restriction. -/
theorem selectedDomainFactor_comp_ι
    (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B)
    (S : A.presentation.atlas.OriginalChartDomain)
    (hS : ∀ c : A.presentation.atlas.SubspaceChart S.carrier, c.val ∈ P) :
    domainInclusion A S ≫ (sourceHomι P f : ofPresentation A ⟶ ofPresentation B) =
      strongFunctor.map (selectedDomainFactor P S hS ≫ f) := by
  change strongFunctor.map (A.originalDomainInclusion S) ≫ sourceHomι P f = _
  erw [← selectedDomainFactor_comp_inclusion P S hS,
    Functor.map_comp, Category.assoc, strongFunctor_map_inclusion_comp_ι,
    ← Functor.map_comp]

/-- Whole original charts in a numerator's selection have genuine full
strong representatives, rather than only seminorm-point representatives. -/
theorem selectedChartFactor_comp_ι
    (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B)
    (i : A.presentation.atlas.Index) (hi : i ∈ P) :
    domainInclusion A (ofChart i) ≫
        (sourceHomι P f : ofPresentation A ⟶ ofPresentation B) =
      strongFunctor.map (selectedChartFactor P i hi ≫ f) :=
  selectedDomainFactor_comp_ι P f (ofChart i) _

/-- Full strong representatives of a quotient arrow on a locally refining
family of its original whole chart domains. No global strong map is assumed. -/
structure ChartRepresentation (F : ofPresentation A ⟶ ofPresentation B) where
  selection : A.presentation.atlas.RefiningSelection
  localMap : ∀ i : {i : A.presentation.atlas.Index // i ∈ selection},
    A.originalDomain (ofChart i.val) ⟶ B
  represents : ∀ i, domainInclusion A (ofChart i.val) ≫ F =
    strongFunctor.map (localMap i)

/-- Every actual quotient arrow has whole-chart full strong representatives,
constructed by selecting a numerator and using its downward-closed charts. -/
theorem nonempty_chartRepresentation (F : ofPresentation A ⟶ ofPresentation B) :
    Nonempty (ChartRepresentation F) := by
  change SourceHomQuotient A B at F
  refine Quotient.inductionOn F ?_
  rintro ⟨P, f⟩
  exact ⟨⟨P, fun i => selectedChartFactor P i.val i.property ≫ f,
    fun i => selectedChartFactor_comp_ι P f i.val i.property⟩⟩

/-- Choose the constructed local representation of an arbitrary quotient
arrow. Every chart algebra in its source is still an original one. -/
def chartRepresentation (F : ofPresentation A ⟶ ofPresentation B) :
    ChartRepresentation F :=
  Classical.choice (nonempty_chartRepresentation F)

end SourceCategory
end Langlands.Analytic.SaturatedAtlasPresentation
