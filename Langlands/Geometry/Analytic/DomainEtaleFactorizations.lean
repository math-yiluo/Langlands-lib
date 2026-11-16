import Langlands.Geometry.Analytic.QuasiEtaleCompactCharts

/-! # Domain embeddings and their étale factorizations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual comparison from a nested domain to its ambient-image domain. -/
def domainNestedLocalizationIso (S : SaturatedAtlasPresentation.{u, v, w} K)
    (D : S.AnalyticDomain) (E : (S.domain D).AnalyticDomain) :
    localizationFunctor.obj ((S.domain D).domain E) ≅
      localizationFunctor.obj (S.domain (D.subspaceExtend E)) :=
  SourceCategory.comparisonFunctor.mapIso (SourceCategory.domainNestedIso D E).symm

@[reassoc]
theorem domainNestedLocalizationIso_hom_inclusion
    (S : SaturatedAtlasPresentation.{u, v, w} K)
    (D : S.AnalyticDomain) (E : (S.domain D).AnalyticDomain) :
    (domainNestedLocalizationIso S D E).hom ≫
        S.localizedDomainInclusion (D.subspaceExtend E) =
      (S.domain D).localizedDomainInclusion E ≫ S.localizedDomainInclusion D := by
  have hh := congrArg SourceCategory.comparisonFunctor.map
    (SourceCategory.domainNestedInverse_ambientInclusion (A := S) D E)
  have hD := S.comparisonFunctor_map_domainInclusion D
  have hE := (S.originalDomain D).comparisonFunctor_map_domainInclusion E
  have hDE := S.comparisonFunctor_map_domainInclusion (D.subspaceExtend E)
  exact (congrArg ((domainNestedLocalizationIso S D E).hom ≫ ·) hDE).symm.trans
    ((SourceCategory.comparisonFunctor.map_comp _ _).symm.trans
      (hh.trans ((SourceCategory.comparisonFunctor.map_comp _ _).trans
        (congrArg₂ (· ≫ ·) hE hD))))

/-- An isomorphism identifies a domain with the inverse image under its inverse. -/
def domainImageIso {U V : LocalizedCategory.{u, v, w} (K := K)}
    (e : U ≅ V) (D : (presentationOf U).AnalyticDomain) :
    domainObj U D ≅ domainObj V (domainPreimage e.inv D) :=
  (domainPreimageIso e.symm D).symm

@[reassoc]
theorem domainImageIso_hom_inclusion {U V : LocalizedCategory.{u, v, w} (K := K)}
    (e : U ≅ V) (D : (presentationOf U).AnalyticDomain) :
    (domainImageIso e D).hom ≫ domainι V (domainPreimage e.inv D) =
      domainι U D ≫ e.hom := by
  apply (cancel_epi (domainPreimageIso e.symm D).hom).1
  change (domainPreimageIso e.symm D).hom ≫
      ((domainPreimageIso e.symm D).inv ≫ domainι V (domainPreimage e.inv D)) =
    (domainPreimageIso e.symm D).hom ≫ (domainι U D ≫ e.hom)
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, domainPreimageIso_hom_inclusion,
    Category.assoc]
  simp only [Iso.symm_hom, e.inv_hom_id, Category.comp_id]

/-- A source isomorphism followed by an actual analytic-domain inclusion. -/
def IsAnalyticDomainEmbedding {U V : LocalizedCategory.{u, v, w} (K := K)}
    (j : U ⟶ V) : Prop :=
  ∃ (D : (presentationOf V).AnalyticDomain) (e : U ≅ domainObj V D),
    j = e.hom ≫ domainι V D

theorem isAnalyticDomainEmbedding_domainι
    (U : LocalizedCategory.{u, v, w} (K := K))
    (D : (presentationOf U).AnalyticDomain) :
    IsAnalyticDomainEmbedding (domainι U D) :=
  ⟨D, Iso.refl _, (Category.id_comp _).symm⟩

theorem IsAffinoidDomainEmbedding.isAnalyticDomainEmbedding
    {U V : LocalizedCategory.{u, v, w} (K := K)}
    {j : U ⟶ V} (hj : IsAffinoidDomainEmbedding j) :
    IsAnalyticDomainEmbedding j := by
  obtain ⟨i, e, he⟩ := hj
  exact ⟨(presentationOf V).chartDomain i, e, he⟩

theorem IsAnalyticDomainEmbedding.iso_comp
    {U V W : LocalizedCategory.{u, v, w} (K := K)}
    {j : V ⟶ W} (hj : IsAnalyticDomainEmbedding j) (e : U ≅ V) :
    IsAnalyticDomainEmbedding (e.hom ≫ j) := by
  obtain ⟨D, e', rfl⟩ := hj
  exact ⟨D, e ≪≫ e', (Category.assoc _ _ _).symm⟩

/-- Restricting the source of a domain embedding is again a domain embedding. -/
theorem IsAnalyticDomainEmbedding.domainι_comp
    {U V : LocalizedCategory.{u, v, w} (K := K)}
    {j : U ⟶ V} (hj : IsAnalyticDomainEmbedding j)
    (D : (presentationOf U).AnalyticDomain) :
    IsAnalyticDomainEmbedding (domainι U D ≫ j) := by
  obtain ⟨C, e, rfl⟩ := hj
  let E : (presentationOf (domainObj V C)).AnalyticDomain := domainPreimage e.inv D
  let a : domainObj U D ≅ domainObj (domainObj V C) E := domainImageIso e D
  let b : domainObj (domainObj V C) E ≅ domainObj V (C.subspaceExtend E) :=
    domainNestedLocalizationIso (presentationOf V) C E
  have ha : a.hom ≫ domainι (domainObj V C) E = domainι U D ≫ e.hom :=
    domainImageIso_hom_inclusion e D
  have hb : b.hom ≫ domainι V (C.subspaceExtend E) =
      domainι (domainObj V C) E ≫ domainι V C :=
    domainNestedLocalizationIso_hom_inclusion (presentationOf V) C E
  refine ⟨C.subspaceExtend E, a ≪≫ b, ?_⟩
  change domainι U D ≫ (e.hom ≫ domainι V C) =
    (a.hom ≫ b.hom) ≫ domainι V (C.subspaceExtend E)
  rw [Category.assoc a.hom, hb, ← Category.assoc a.hom, ha, Category.assoc]

/-- Domain embeddings are closed under composition. -/
theorem IsAnalyticDomainEmbedding.comp
    {U V W : LocalizedCategory.{u, v, w} (K := K)}
    {j : U ⟶ V} {k : V ⟶ W}
    (hj : IsAnalyticDomainEmbedding j) (hk : IsAnalyticDomainEmbedding k) :
    IsAnalyticDomainEmbedding (j ≫ k) := by
  obtain ⟨D, e, rfl⟩ := hj
  rw [Category.assoc]
  exact (hk.domainι_comp D).iso_comp e

/-- A map which identifies its source with an analytic domain in an étale
space over its target. This retains the factorization data needed by domains. -/
def HasDomainEtaleFactorization {U X : LocalizedCategory.{u, v, v} (K := K)}
    (f : U ⟶ X) : Prop :=
  ∃ (W : LocalizedCategory.{u, v, v} (K := K)) (j : U ⟶ W) (g : W ⟶ X),
    IsAnalyticDomainEmbedding j ∧ etale g ∧ j ≫ g = f

theorem HasDomainEtaleFactorization.quasiEtale
    {U X : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ X} (hf : HasDomainEtaleFactorization f) : quasiEtale f := by
  obtain ⟨W, j, g, ⟨D, e, rfl⟩, hg, rfl⟩ := hf
  rw [Category.assoc]
  exact ((SaturatedAtlasPresentation.quasiEtale (K := K)).cancel_left_of_respectsIso _ _).mpr
    (quasiEtale_domainι_comp_of_etale D g hg)

/-- Every further actual source domain retains the explicit étale envelope. -/
theorem HasDomainEtaleFactorization.domainι_comp
    {U X : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ X} (hf : HasDomainEtaleFactorization f)
    (D : (presentationOf U).AnalyticDomain) :
    HasDomainEtaleFactorization (domainι U D ≫ f) := by
  obtain ⟨W, j, g, hj, hg, rfl⟩ := hf
  exact ⟨W, domainι U D ≫ j, g, hj.domainι_comp D, hg,
    Category.assoc _ _ _⟩

theorem HasDomainEtaleFactorization.iso_comp
    {U V X : LocalizedCategory.{u, v, v} (K := K)}
    {f : V ⟶ X} (hf : HasDomainEtaleFactorization f) (e : U ≅ V) :
    HasDomainEtaleFactorization (e.hom ≫ f) := by
  obtain ⟨W, j, g, hj, hg, rfl⟩ := hf
  exact ⟨W, e.hom ≫ j, g, hj.iso_comp e, hg, Category.assoc _ _ _⟩

theorem HasDomainEtaleFactorization.comp_iso
    {U X Y : LocalizedCategory.{u, v, v} (K := K)}
    {f : U ⟶ X} (hf : HasDomainEtaleFactorization f) (e : X ≅ Y) :
    HasDomainEtaleFactorization (f ≫ e.hom) := by
  obtain ⟨W, j, g, hj, hg, rfl⟩ := hf
  exact ⟨W, j, g ≫ e.hom, hj,
    ((etale (K := K)).cancel_right_of_respectsIso _ _).mpr hg,
    (Category.assoc _ _ _).symm⟩

end Langlands.Analytic.SaturatedAtlasPresentation
