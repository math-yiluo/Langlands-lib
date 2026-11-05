import Langlands.Geometry.Analytic.SaturatedSourceDomainSeparation
import Langlands.Geometry.Analytic.OriginalDomainLocalization
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! # The actual quotient-Hom presheaf on original-chart domains -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory Set
open IndexedAffinoidAtlas.OriginalChartDomain
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- The actual quotient arrow between two nested domain objects, constructed
from the proved image-only factorization property. -/
def domainMap {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T) :
    ofPresentation (A.originalDomain S) ⟶ ofPresentation (A.originalDomain T) :=
  domainLift T (domainInclusion A S) (by
    intro x
    erw [domainInclusion_apply]
    exact hST x.property)

@[simp]
theorem domainMap_inclusion {S T : A.presentation.atlas.OriginalChartDomain}
    (hST : S ≤ T) :
    domainMap hST ≫ domainInclusion A T = domainInclusion A S :=
  domainLift_comp_inclusion T _ _

@[simp]
theorem domainMap_apply_val {S T : A.presentation.atlas.OriginalChartDomain}
    (hST : S ≤ T) (x : S.carrier) :
    (spaceFunctor.map (domainMap hST) x).val = x.val := by
  change (spaceFunctor.map (domainLift T (domainInclusion A S) _) x).val = x.val
  erw [domainLift_apply, domainInclusion_apply]

@[simp]
theorem domainMap_id (S : A.presentation.atlas.OriginalChartDomain) :
    domainMap (le_refl S) = 𝟙 (ofPresentation (A.originalDomain S)) := by
  apply (cancel_mono (domainInclusion A S)).1
  erw [domainMap_inclusion, Category.id_comp]

@[simp]
theorem domainMap_comp {S T U : A.presentation.atlas.OriginalChartDomain}
    (hST : S ≤ T) (hTU : T ≤ U) :
    domainMap hST ≫ domainMap hTU = domainMap (hST.trans hTU) := by
  apply (cancel_mono (domainInclusion A U)).1
  erw [Category.assoc, domainMap_inclusion, domainMap_inclusion, domainMap_inclusion]

/-- Realize each actual domain by its saturated subspace presentation and
each subset inclusion by the constructed quotient arrow. -/
def domainFunctor (A : SaturatedAtlasPresentation.{u, v, w} K) :
    A.presentation.atlas.OriginalChartDomain ⥤ SourceCategory.{u, v, w} K where
  obj S := ofPresentation (A.originalDomain S)
  map f := domainMap (leOfHom f)
  map_id S := domainMap_id S
  map_comp f g := (domainMap_comp (leOfHom f) (leOfHom g)).symm

/-- Maps from every actual domain into a fixed target, with restrictions
given by precomposition in the actual source-quotient category. -/
def domainHomPresheaf (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    A.presentation.atlas.OriginalChartDomainᵒᵖ ⥤ Type (max u v w) :=
  (domainFunctor A).op ⋙ yoneda.obj (ofPresentation B)

@[simp]
theorem domainHomPresheaf_obj (S : A.presentation.atlas.OriginalChartDomain) :
    (domainHomPresheaf A B).obj (Opposite.op S) =
      (ofPresentation (A.originalDomain S) ⟶ ofPresentation B) := rfl

@[simp]
theorem domainHomPresheaf_map {S T : A.presentation.atlas.OriginalChartDomain}
    (f : S ⟶ T) (F : ofPresentation (A.originalDomain T) ⟶ ofPresentation B) :
    (domainHomPresheaf A B).map f.op F = domainMap (leOfHom f) ≫ F := rfl

/-- Postcomposition with an arbitrary quotient arrow acts naturally on
domain-valued Hom presheaves. -/
def domainHomPresheafMap (F : ofPresentation B ⟶ ofPresentation C) :
    domainHomPresheaf A B ⟶ domainHomPresheaf A C :=
  Functor.whiskerLeft (domainFunctor A).op (yoneda.map F)

/-- Localizing a relative domain cover to its actual target subspace keeps
all finite neighborhood witnesses. -/
theorem relativeDomainCover_subspace
    (S : A.presentation.atlas.OriginalChartDomain) {ι : Type z}
    (D : ι → A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier}) :
    AtlasTopology.LocallyRefines
      (Set.range (fun k => (S.subspaceRestrict ⟨D k, hDS k⟩).carrier)) {Set.univ} := by
  have hQ := (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr hD
  intro V hV x _hx
  obtain rfl := Set.mem_singleton_iff.mp hV
  obtain ⟨σ, hf, hs, hm, hn⟩ := hQ x
  refine ⟨σ, hf, ?_, fun W hW => ⟨Set.subset_univ _, hm W hW⟩, ?_⟩
  · intro W hW
    obtain ⟨T, ⟨k, rfl⟩, _hTS, rfl⟩ := hs hW
    exact ⟨k, rfl⟩
  · simpa only [nhdsWithin_univ] using hn

/-- The double-subspace inclusion factors through the corresponding ambient
domain, by the proved domain universal property. -/
def relativeDomainComparison (S T : A.presentation.atlas.OriginalChartDomain)
    (hTS : T ≤ S) :
    ofPresentation ((A.originalDomain S).originalDomain
        (S.subspaceRestrict ⟨T, hTS⟩)) ⟶ ofPresentation (A.originalDomain T) :=
  domainLift T
    (domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩) ≫
      domainInclusion A S) (by
    intro x
    erw [Functor.map_comp]
    change spaceFunctor.map (domainInclusion A S)
      (spaceFunctor.map
        (domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩)) x) ∈ T
    erw [domainInclusion_apply, domainInclusion_apply]
    exact x.property)

/-- The comparison commutes with the inclusion into the intermediate domain
as an equality of complete quotient arrows. -/
@[simp]
theorem relativeDomainComparison_map (S T : A.presentation.atlas.OriginalChartDomain)
    (hTS : T ≤ S) :
    relativeDomainComparison S T hTS ≫ domainMap hTS =
      domainInclusion (A.originalDomain S) (S.subspaceRestrict ⟨T, hTS⟩) := by
  apply (cancel_mono (domainInclusion A S)).1
  erw [Category.assoc, domainMap_inclusion]
  exact domainLift_comp_inclusion T _ _

/-- Quotient arrows out of any actual domain are determined by restrictions
to a quasinet family of ambient domains covering that domain. -/
theorem eq_of_relativeDomainCover
    (S : A.presentation.atlas.OriginalChartDomain) {ι : Type z}
    (D : ι → A.presentation.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier})
    (F G : ofPresentation (A.originalDomain S) ⟶ ofPresentation B)
    (h : ∀ k, domainMap (hDS k) ≫ F = domainMap (hDS k) ≫ G) : F = G := by
  apply eq_of_domainCover (fun k => S.subspaceRestrict ⟨D k, hDS k⟩)
    (relativeDomainCover_subspace S D hDS hD) F G
  intro k
  have heq := congrArg
    (fun r : ofPresentation (A.originalDomain (D k)) ⟶ ofPresentation B =>
      relativeDomainComparison S (D k) (hDS k) ≫ r) (h k)
  simpa only [← Category.assoc, relativeDomainComparison_map] using heq

/-- Equality on every arrow of any quasinet covering sieve detects equality
of domain-valued quotient morphisms. -/
theorem eq_of_domainCoveringSieve
    {S : A.presentation.atlas.OriginalChartDomain} (R : Sieve S)
    (hR : R ∈ quasinetTopology A.presentation.atlas S)
    (F G : ofPresentation (A.originalDomain S) ⟶ ofPresentation B)
    (h : ∀ {T} (f : T ⟶ S), R f →
      domainMap (leOfHom f) ≫ F = domainMap (leOfHom f) ≫ G) : F = G := by
  let ι := {T : A.presentation.atlas.OriginalChartDomain //
    ∃ hTS : T ≤ S, R (homOfLE hTS)}
  let D : ι → A.presentation.atlas.OriginalChartDomain := fun k => k.val
  let hDS : ∀ k : ι, D k ≤ S := fun k => Classical.choose k.property
  have hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {S.carrier} := by
    apply AtlasTopology.LocallyRefines.mono hR ?_ Subset.rfl
    rintro U ⟨T, hTS, hRT, rfl⟩
    exact ⟨⟨T, hTS, hRT⟩, rfl⟩
  apply eq_of_relativeDomainCover S D hDS hD F G
  intro k
  exact h (homOfLE (hDS k)) (Classical.choose_spec k.property)

/-- The actual quotient-Hom presheaf is separated for every covering sieve
of the original-chart quasinet topology. This asserts uniqueness of gluing. -/
theorem domainHomPresheaf_isSeparated (A B : SaturatedAtlasPresentation.{u, v, w} K) :
    Presieve.IsSeparated (quasinetTopology A.presentation.atlas)
      (domainHomPresheaf A B) := by
  intro S R hR x F G hF hG
  apply eq_of_domainCoveringSieve R hR F G
  intro T f hf
  exact (hF f hf).trans (hG f hf).symm

end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory
