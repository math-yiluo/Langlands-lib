import Langlands.Geometry.Analytic.OriginalDomainRefinedStrongDescent
import Langlands.Geometry.Analytic.SaturatedSourceDomainSeparation

/-! # Unique quotient gluing of literal full strong domain matching families -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- The complete strong comparison between the same actual domain with selected
source charts and with its original charts. -/
def originalDomainRefiningMap (P : A.presentation.atlas.RefiningSelection)
    (S : A.presentation.atlas.OriginalChartDomain) :
    (A.refiningSubpresentation P).originalDomain
        (A.presentation.atlas.originalDomainSubatlasOrderIso
          P.carrier P.locally_refining S) ⟶ A.originalDomain S :=
  A.presentation.originalDomainStrongSubatlasMap P.carrier P.locally_refining S

theorem isQuasiIso_originalDomainRefiningMap
    (P : A.presentation.atlas.RefiningSelection)
    (S : A.presentation.atlas.OriginalChartDomain) :
    (originalDomainRefiningMap (A := A) P S).IsQuasiIso :=
  A.presentation.isQuasiIso_originalDomainStrongSubatlasMap
    P.carrier P.locally_refining S

/-- Comparing domain atlases then composing retains every local bounded map
at the identical original source chart. -/
theorem originalDomainRefiningMap_comp
    (P : A.presentation.atlas.RefiningSelection)
    (S : A.presentation.atlas.OriginalChartDomain) (f : A.originalDomain S ⟶ B) :
    originalDomainRefiningMap P S ≫ f =
      f.restrictSelectedDomainSource P.carrier P.locally_refining := by
  refine StrongHom.ext_of_saturated
    ((A.refiningSubpresentation P).originalDomain _).hasAllLocalDomains rfl ?_
  intro i
  let j : (A.originalDomain S).presentation.atlas.Index := ⟨i.val.val, i.property⟩
  obtain ⟨k, hf⟩ := f.target_exists j
  have hc : (originalDomainRefiningMap (A := A) P S).baseMap ''
      Set.range (((A.refiningSubpresentation P).originalDomain _).presentation.atlas.chart i) ⊆
        Set.range ((A.originalDomain S).presentation.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hcomp := (originalDomainRefiningMap (A := A) P S).comp_admissible f i j k hc hf
  refine ⟨k, hcomp, ?_⟩
  refine (StrongHom.saturatedComp_pullback (originalDomainRefiningMap P S) f
    ((A.refiningSubpresentation P).originalDomain _).hasAllLocalDomains
    (A.originalDomain S).hasAllLocalDomains i j k hc hf hcomp).trans ?_
  change (A.presentation.atlas.restriction i.val.val i.val.val _).comp
    (f.pullback j k hf) = f.pullback j k _
  rw [A.presentation.atlas.restriction_id]
  erw [BoundedAlgHom.id_comp]

/-- The full domain comparison commutes with the ambient same-space inclusion,
as equality of complete strong maps. -/
theorem originalDomainRefiningMap_inclusion
    (P : A.presentation.atlas.RefiningSelection)
    (S : A.presentation.atlas.OriginalChartDomain) :
    originalDomainRefiningMap P S ≫ A.originalDomainInclusion S =
      (A.refiningSubpresentation P).originalDomainInclusion
          (A.presentation.atlas.originalDomainSubatlasOrderIso
            P.carrier P.locally_refining S) ≫ A.refiningSubatlasInclusion P := by
  erw [originalDomainRefiningMap_comp, originalDomainInclusion_comp_eq_restrictSubspace]
  refine StrongHom.ext_of_pullback rfl ?_
  intro i j h h'
  rfl

namespace SourceCategory

variable {ι : Type z} {D : ι → A.presentation.atlas.OriginalChartDomain}

/-- The quotient arrow represented by the full numerator on the source selection
constructed from the actual domain cover. -/
def glueStrongDomainFamily
    (d : A.presentation.OriginalDomainStrongMatchingFamily B.presentation D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    ofPresentation A ⟶ ofPresentation B :=
  sourceHomι (domainCoverSourceSelection D hD) (d.refinedGlue hD)

/-- The constructed quotient arrow recovers every given local strong map in
the source quotient, by canceling the inverted domain comparison. -/
theorem glueStrongDomainFamily_restrict
    (d : A.presentation.OriginalDomainStrongMatchingFamily B.presentation D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) (k : ι) :
    domainInclusion A (D k) ≫ glueStrongDomainFamily d hD =
      strongFunctor.map (d.localMap k) := by
  let P := domainCoverSourceSelection D hD
  let E := A.presentation.atlas.originalDomainSubatlasOrderIso
    P.carrier P.locally_refining (D k)
  let c : (A.refiningSubpresentation P).originalDomain E ⟶ A.originalDomain (D k) :=
    originalDomainRefiningMap P (D k)
  have : IsIso (strongFunctor.map c) :=
    Localization.inverts strongFunctor (quasiIsomorphisms (K := K))
      c (isQuasiIso_originalDomainRefiningMap P (D k))
  apply (cancel_epi (strongFunctor.map c)).1
  change strongFunctor.map c ≫
      (strongFunctor.map (A.originalDomainInclusion (D k)) ≫
        (sourceHomι P (d.refinedGlue hD))) =
    strongFunctor.map c ≫ strongFunctor.map (d.localMap k)
  erw [← Category.assoc, ← Functor.map_comp]
  change strongFunctor.map
      (originalDomainRefiningMap P (D k) ≫ A.originalDomainInclusion (D k)) ≫
        sourceHomι P (d.refinedGlue hD) = _
  erw [originalDomainRefiningMap_inclusion, Functor.map_comp, Category.assoc,
    strongFunctor_map_inclusion_comp_ι, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  erw [originalDomainInclusion_comp_eq_restrictSubspace,
    originalDomainRefiningMap_comp]
  exact d.refinedGlue_restrictSubspace hD k

/-- Domain-cover separation compares the constructed glue with every possible
quotient arrow having the prescribed local restrictions. -/
theorem glueStrongDomainFamily_unique
    (d : A.presentation.OriginalDomainStrongMatchingFamily B.presentation D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ})
    (F : ofPresentation A ⟶ ofPresentation B)
    (hF : ∀ k, domainInclusion A (D k) ≫ F = strongFunctor.map (d.localMap k)) :
    F = glueStrongDomainFamily d hD :=
  eq_of_domainCover D hD F (glueStrongDomainFamily d hD)
    (fun k => (hF k).trans (glueStrongDomainFamily_restrict d hD k).symm)

/-- Literal full strong matching families over every original-domain quasinet
cover have a unique glue among all arrows of the actual source quotient. -/
theorem existsUnique_glueStrongDomainFamily
    (d : A.presentation.OriginalDomainStrongMatchingFamily B.presentation D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    ∃! F : ofPresentation A ⟶ ofPresentation B,
      ∀ k, domainInclusion A (D k) ≫ F = strongFunctor.map (d.localMap k) :=
  ⟨glueStrongDomainFamily d hD, glueStrongDomainFamily_restrict d hD,
    fun F hF => glueStrongDomainFamily_unique d hD F hF⟩

end SourceCategory
end Langlands.Analytic.SaturatedAtlasPresentation
