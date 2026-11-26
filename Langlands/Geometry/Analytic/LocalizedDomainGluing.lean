import Langlands.Geometry.Analytic.QuotientDomainGluing
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Gluing analytic maps along original-chart domains in the localized category -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K} {ι : Type z}

/-- The analytic map between two nested original-chart domains. -/
def localizedDomainMap {D E : A.AnalyticDomain} (h : D ≤ E) :
    localizationFunctor.obj (A.domain D) ⟶ localizationFunctor.obj (A.domain E) :=
  SourceCategory.comparisonFunctor.map (SourceCategory.domainMap h)

@[reassoc (attr := simp)]
theorem localizedDomainMap_inclusion {D E : A.AnalyticDomain} (h : D ≤ E) :
    localizedDomainMap h ≫ A.localizedDomainInclusion E = A.localizedDomainInclusion D := by
  calc
    _ = SourceCategory.comparisonFunctor.map
          (SourceCategory.domainMap h ≫ SourceCategory.domainInclusion A E) := by
      rw [localizedDomainMap, ← A.comparisonFunctor_map_domainInclusion]
      exact (Functor.map_comp _ _ _).symm
    _ = _ := by
      rw [SourceCategory.domainMap_inclusion]
      exact A.comparisonFunctor_map_domainInclusion D

/-- Analytic maps on given source domains, with equality of their restrictions
to each intersection in the localized category. -/
structure LocalizedDomainMatchingFamily (A B : SaturatedAtlasPresentation.{u, v, w} K)
    (D : ι → A.AnalyticDomain) where
  localMap : ∀ i, localizationFunctor.obj (A.domain (D i)) ⟶ localizationFunctor.obj B
  overlap : ∀ i j,
    localizedDomainMap (inf_le_left : D i ⊓ D j ≤ D i) ≫ localMap i =
      localizedDomainMap (inf_le_right : D i ⊓ D j ≤ D j) ≫ localMap j

namespace LocalizedDomainMatchingFamily

variable {D : ι → A.AnalyticDomain}

private def toQuotient (d : LocalizedDomainMatchingFamily A B D) :
    SourceCategory.QuotientDomainMatchingFamily A B D where
  localMap i := SourceCategory.comparisonFunctor.preimage (d.localMap i)
  overlap i j := SourceCategory.comparisonFunctor.map_injective (by
    simp only [Functor.map_comp]
    erw [Functor.map_preimage, Functor.map_preimage]
    exact d.overlap i j)

/-- Glue analytic maps on a quasinet cover through the explicit source quotient. -/
def glue (d : LocalizedDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines (Set.range fun i => (D i).carrier) {Set.univ}) :
    localizationFunctor.obj A ⟶ localizationFunctor.obj B :=
  SourceCategory.comparisonFunctor.map (d.toQuotient.glue hD)

@[reassoc]
theorem glue_restrict (d : LocalizedDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines (Set.range fun i => (D i).carrier) {Set.univ}) (i : ι) :
    A.localizedDomainInclusion (D i) ≫ d.glue hD = d.localMap i := by
  have h := congrArg SourceCategory.comparisonFunctor.map (d.toQuotient.glue_restrict hD i)
  simp only [Functor.map_comp, A.comparisonFunctor_map_domainInclusion, toQuotient] at h
  erw [Functor.map_preimage] at h
  exact h

end LocalizedDomainMatchingFamily

/-- Equality of localized analytic morphisms can be checked on an original-chart
quasinet cover of the source. -/
theorem localizedHom_ext_of_domainCover (D : ι → A.AnalyticDomain)
    (hD : AtlasTopology.LocallyRefines (Set.range fun i => (D i).carrier) {Set.univ})
    {f g : localizationFunctor.obj A ⟶ localizationFunctor.obj B}
    (h : ∀ i, A.localizedDomainInclusion (D i) ≫ f = A.localizedDomainInclusion (D i) ≫ g) :
    f = g := by
  obtain ⟨F, rfl⟩ := SourceCategory.comparisonFunctor.map_surjective
    (X := SourceCategory.ofPresentation A) (Y := SourceCategory.ofPresentation B) f
  obtain ⟨G, rfl⟩ := SourceCategory.comparisonFunctor.map_surjective
    (X := SourceCategory.ofPresentation A) (Y := SourceCategory.ofPresentation B) g
  apply congrArg SourceCategory.comparisonFunctor.map
  refine SourceCategory.eq_of_domainCover D hD F G fun i =>
    SourceCategory.comparisonFunctor.map_injective ?_
  simp only [Functor.map_comp, A.comparisonFunctor_map_domainInclusion]
  exact h i

end Langlands.Analytic.SaturatedAtlasPresentation
