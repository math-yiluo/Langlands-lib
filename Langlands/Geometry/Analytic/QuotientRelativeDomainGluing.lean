import Langlands.Geometry.Analytic.QuotientDomainGluing

/-! # Gluing quotient morphisms on relative original-domain covers -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory Set AffinoidAtlasPresentation
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- The comparison from a relative domain's nested realization has the actual
ambient inclusion as its composite inclusion. -/
@[simp]
theorem relativeDomainComparison_inclusion
    (S T : A.presentation.atlas.OriginalChartDomain) (hTS : T ≤ S) :
    relativeDomainComparison S T hTS ≫ domainInclusion A T =
      domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩) ≫
        domainInclusion A S :=
  domainLift_comp_inclusion T _ _

/-- Insert the intermediate subspace membership for an ambient domain
contained in that subspace, using actual quotient-domain factorization. -/
def relativeDomainInverse (S T : A.presentation.atlas.OriginalChartDomain)
    (hTS : T ≤ S) :
    ofPresentation (A.originalDomain T) ⟶
      ofPresentation ((A.originalDomain S).originalDomain
        (S.subspaceRestrict ⟨T, hTS⟩)) :=
  domainLift (S.subspaceRestrict ⟨T, hTS⟩) (domainMap hTS) (by
    intro x
    change (spaceFunctor.map (domainMap hTS) x).val ∈ T
    erw [domainMap_apply_val]
    exact x.property)

@[simp]
theorem relativeDomainInverse_inclusion
    (S T : A.presentation.atlas.OriginalChartDomain) (hTS : T ≤ S) :
    relativeDomainInverse S T hTS ≫
        domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩) =
      domainMap hTS :=
  domainLift_comp_inclusion _ _ _

set_option maxHeartbeats 800000 in
/-- The nested and ambient realizations of every relative domain are
isomorphic as actual quotient objects, retaining all morphism data. -/
def relativeDomainIso (S T : A.presentation.atlas.OriginalChartDomain)
    (hTS : T ≤ S) :
    ofPresentation ((A.originalDomain S).originalDomain
        (S.subspaceRestrict ⟨T, hTS⟩)) ≅ ofPresentation (A.originalDomain T) where
  hom := relativeDomainComparison S T hTS
  inv := relativeDomainInverse S T hTS
  hom_inv_id := by
    have : Mono (domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩)) :=
      domainInclusion_mono (B := A.originalDomain S) _
    apply (cancel_mono
      (domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩))).1
    erw [Category.assoc, relativeDomainInverse_inclusion,
      relativeDomainComparison_map, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (domainInclusion A T)).1
    erw [Category.assoc, relativeDomainComparison_inclusion, ← Category.assoc,
      relativeDomainInverse_inclusion, domainMap_inclusion, Category.id_comp]

set_option maxHeartbeats 800000 in
/-- The full quotient comparison commutes with inclusion between any two
ambient domains lying in the fixed intermediate domain. -/
theorem relativeDomainComparison_naturality
    (S : A.presentation.atlas.OriginalChartDomain)
    {T U : A.presentation.atlas.OriginalChartDomain}
    (hTS : T ≤ S) (hUS : U ≤ S) (hTU : T ≤ U) :
    domainMap (show S.subspaceRestrict ⟨T, hTS⟩ ≤
      S.subspaceRestrict ⟨U, hUS⟩ from fun _ hx => hTU hx) ≫
        relativeDomainComparison S U hUS =
      relativeDomainComparison S T hTS ≫ domainMap hTU := by
  apply (cancel_mono (domainInclusion A U)).1
  erw [Category.assoc, relativeDomainComparison_inclusion, ← Category.assoc,
    domainMap_inclusion (A := A.originalDomain S), Category.assoc,
    domainMap_inclusion (A := A), relativeDomainComparison_inclusion]

namespace QuotientDomainMatchingFamily

variable {ι : Type z} {D : ι → A.presentation.atlas.OriginalChartDomain}

/-- Transport every arbitrary local quotient arrow to the actual domain
subspace. Naturality and the original overlap equations prove matching. -/
def onSubspace (d : QuotientDomainMatchingFamily A B D)
    (S : A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S) :
    QuotientDomainMatchingFamily (A.originalDomain S) B
      (fun k => S.subspaceRestrict ⟨D k, hDS k⟩) where
  localMap k := relativeDomainComparison S (D k) (hDS k) ≫ d.localMap k
  overlap k l := by
    have hIS : D k ⊓ D l ≤ S := inf_le_left.trans (hDS k)
    have hk := relativeDomainComparison_naturality S hIS (hDS k) inf_le_left
    have hl := relativeDomainComparison_naturality S hIS (hDS l) inf_le_right
    erw [← Category.assoc, hk, Category.assoc,
      ← Category.assoc _ (relativeDomainComparison S (D l) (hDS l)), hl,
      Category.assoc]
    exact congrArg (fun F => relativeDomainComparison S (D k ⊓ D l) hIS ≫ F)
      (d.overlap k l)

/-- Construct a quotient morphism on a domain from arbitrary matching
quotient arrows on a relative quasinet cover of that domain. -/
def glueRelative (d : QuotientDomainMatchingFamily A B D)
    (S : A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier}) :
    ofPresentation (A.originalDomain S) ⟶ ofPresentation B :=
  (d.onSubspace S hDS).glue (relativeDomainCover_subspace S D hDS hD)

/-- The constructed relative glue recovers each original local quotient
arrow, by cancelling its actual subspace comparison isomorphism. -/
theorem glueRelative_restrict (d : QuotientDomainMatchingFamily A B D)
    (S : A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier}) (k : ι) :
    domainMap (hDS k) ≫ d.glueRelative S hDS hD = d.localMap k := by
  have : IsIso (relativeDomainComparison S (D k) (hDS k)) := by
    change IsIso (relativeDomainIso S (D k) (hDS k)).hom
    infer_instance
  apply (cancel_epi (relativeDomainComparison S (D k) (hDS k))).1
  erw [← Category.assoc, relativeDomainComparison_map]
  exact (d.onSubspace S hDS).glue_restrict
    (relativeDomainCover_subspace S D hDS hD) k

/-- Relative-domain quotient gluing is unique among arbitrary quotient
morphisms, by full separation on the supplied relative cover. -/
theorem glueRelative_unique (d : QuotientDomainMatchingFamily A B D)
    (S : A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier})
    (F : ofPresentation (A.originalDomain S) ⟶ ofPresentation B)
    (hF : ∀ k, domainMap (hDS k) ≫ F = d.localMap k) :
    F = d.glueRelative S hDS hD :=
  eq_of_relativeDomainCover S D hDS hD F (d.glueRelative S hDS hD)
    (fun k => (hF k).trans (d.glueRelative_restrict S hDS hD k).symm)

/-- Every relative-domain quasinet matching family has a unique glue in the
actual quotient category. -/
theorem existsUnique_glueRelative (d : QuotientDomainMatchingFamily A B D)
    (S : A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier}) :
    ∃! F : ofPresentation (A.originalDomain S) ⟶ ofPresentation B,
      ∀ k, domainMap (hDS k) ≫ F = d.localMap k :=
  ⟨d.glueRelative S hDS hD, d.glueRelative_restrict S hDS hD,
    fun F hF => d.glueRelative_unique S hDS hD F hF⟩

end QuotientDomainMatchingFamily
end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory
