import Langlands.Geometry.Analytic.RecognizedAtlasLocalization
import Langlands.Geometry.Analytic.RecognizedDomainSite
import Langlands.Geometry.Analytic.CompatibleDomainRestriction

/-! # Recognition compares the actual localized domain diagrams -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) {J : Type z} (e : J ≃ a.Index)

/-- The actual domain condition depends on chart ranges, so changing only
 the original indices preserves and reflects it on every literal subset. -/
theorem isOriginalChartDomain_reindex_iff (S : Set X) :
    (a.reindex e).IsOriginalChartDomain S ↔ a.IsOriginalChartDomain S := by
  change AtlasTopology.IsQuasinet
      (AtlasTopology.restrictedFamily (Set.range (fun j => Set.range (a.chart (e j)))) S) ↔ _
  rw [a.reindexed_chartFamily e]
  rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The canonical common-universe source and recognition target have the
 same literal domains. Their index universes need not equal the space universe. -/
theorem recognitionTarget_isOriginalChartDomain_iff (S : Set A.space) :
    A.recognitionTarget.atlas.IsOriginalChartDomain S ↔
      A.saturationSource.atlas.IsOriginalChartDomain S :=
  (A.atlas.recognitionAtlas.isOriginalChartDomain_reindex_iff
    (Equiv.ulift : ULift.{w} A.atlas.RecognizedSubset ≃ A.atlas.RecognizedSubset) S).trans
      ((A.atlas.isOriginalChartDomain_recognitionAtlas_iff S).trans
        (A.atlas.isOriginalChartDomain_reindex_iff
          (Equiv.ulift : ULift.{v} A.atlas.Index ≃ A.atlas.Index) S).symm)

/-- Same-subset comparison of the actual domain orders used by the
 two canonically reindexed presentations. -/
def recognitionLiftedDomainOrderIso :
    A.saturationSource.atlas.OriginalChartDomain ≃o
      A.recognitionTarget.atlas.OriginalChartDomain where
  toFun S := ⟨S.carrier, (A.recognitionTarget_isOriginalChartDomain_iff S.carrier).mpr S.is_domain⟩
  invFun T := ⟨T.carrier, (A.recognitionTarget_isOriginalChartDomain_iff T.carrier).mp T.is_domain⟩
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem coe_recognitionLiftedDomainOrderIso
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    (A.recognitionLiftedDomainOrderIso S).carrier = S.carrier := rfl

/-- Every original contained chart has its original recognized copy
 inside the very same domain. This constructs the target-chart witness. -/
theorem compatibleToRecognition_hasDomainTargets (S : Set A.space) :
    A.compatibleToRecognition.toStrongHom.HasDomainTargets S S := by
  intro c
  let d : A.recognitionTarget.atlas.Index :=
    ULift.up (A.atlas.originalRecognitionIndex c.val.down)
  have hd : Set.range (A.recognitionTarget.atlas.chart d) =
      Set.range (A.saturationSource.atlas.chart c.val) :=
    A.atlas.recognitionAtlas_original_range c.val.down
  refine ⟨⟨d, hd.subset.trans c.property⟩, ?_⟩
  change id '' Set.range (A.saturationSource.atlas.chart c.val) ⊆
    Set.range (A.recognitionTarget.atlas.chart d)
  rw [Set.image_id]
  exact hd.symm.subset

/-- Restrict the actual compatible recognition family to the same literal
 domain on both sides, with all admissible bounded maps unchanged. -/
def compatibleDomainToRecognition
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    A.saturationSource.originalCompatibleDomainFunctor.obj S ⟶
      A.recognitionTarget.originalCompatibleDomainFunctor.obj
        (A.recognitionLiftedDomainOrderIso S) :=
  A.compatibleToRecognition.restrictDomains S.carrier S.carrier S.is_domain
    (A.recognitionLiftedDomainOrderIso S).is_domain
    (by change id '' S.carrier ⊆ S.carrier; rw [Set.image_id])
    (A.compatibleToRecognition_hasDomainTargets S.carrier)

@[simp]
theorem compatibleDomainToRecognition_baseMap
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    (A.compatibleDomainToRecognition S).baseMap = ContinuousMap.id S.carrier := rfl

/-- The full quasi-isomorphism property holds for every actual domain,
 including all original admissible chart pairs. -/
theorem compatibleDomainToRecognition_isQuasiIso
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    (A.compatibleDomainToRecognition S).toStrongHom.IsQuasiIso :=
  A.toRecognition_isQuasiIso.restrictDomains S (A.recognitionLiftedDomainOrderIso S)
    (A.compatibleToRecognition_hasDomainTargets S.carrier)
    (by change id '' S.carrier = S.carrier; exact Set.image_id _)

/-- The unchanged full bounded families commute with every actual domain
 inclusion, before passing to the category of fractions. -/
def compatibleRecognitionDomainComparison :
    A.saturationSource.originalCompatibleDomainFunctor ⟶
      A.recognitionLiftedDomainOrderIso.equivalence.functor ⋙
        A.recognitionTarget.originalCompatibleDomainFunctor where
  app S := A.compatibleDomainToRecognition S
  naturality S T h := by
    exact A.compatibleToRecognition.restrictDomains_naturality
      S.carrier T.carrier S.carrier T.carrier
      S.is_domain T.is_domain
      (A.recognitionLiftedDomainOrderIso S).is_domain
      (A.recognitionLiftedDomainOrderIso T).is_domain
      (leOfHom h) (leOfHom h)
      (by change id '' S.carrier ⊆ S.carrier; rw [Set.image_id])
      (by change id '' T.carrier ⊆ T.carrier; rw [Set.image_id])
      (A.compatibleToRecognition_hasDomainTargets S.carrier)
      (A.compatibleToRecognition_hasDomainTargets T.carrier)

/-- The actual comparison on each domain becomes an isomorphism by
 inverting its proved full quasi-isomorphism. -/
def localizedRecognitionDomainIso
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    CompatibleAtlasPresentation.localizationFunctor.obj
        (A.saturationSource.originalCompatibleDomainFunctor.obj S) ≅
      CompatibleAtlasPresentation.localizationFunctor.obj
        (A.recognitionTarget.originalCompatibleDomainFunctor.obj
          (A.recognitionLiftedDomainOrderIso S)) :=
  CompatibleAtlasPresentation.localizedQuasiIso
    (A.compatibleDomainToRecognition S) (A.compatibleDomainToRecognition_isQuasiIso S)

@[simp]
theorem localizedRecognitionDomainIso_hom
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    (A.localizedRecognitionDomainIso S).hom =
      CompatibleAtlasPresentation.localizationFunctor.map
        (A.compatibleDomainToRecognition S) := rfl

/-- Recognition identifies the entire localized diagram of actual domains,
 with naturality proved as equality of full compatible morphisms. -/
def localizedRecognitionDomainNatIso :
    A.saturationSource.originalCompatibleDomainFunctor ⋙
        CompatibleAtlasPresentation.localizationFunctor ≅
      A.recognitionLiftedDomainOrderIso.equivalence.functor ⋙
        A.recognitionTarget.originalCompatibleDomainFunctor ⋙
          CompatibleAtlasPresentation.localizationFunctor :=
  NatIso.ofComponents (fun S => CompatibleAtlasPresentation.localizedQuasiIso
      (A.compatibleRecognitionDomainComparison.app S)
      (A.compatibleDomainToRecognition_isQuasiIso S)) (by
    intro S T h
    exact (CategoryTheory.Functor.map_comp
      CompatibleAtlasPresentation.localizationFunctor _ _).symm.trans
      ((congrArg CompatibleAtlasPresentation.localizationFunctor.map
        (A.compatibleRecognitionDomainComparison.naturality h)).trans
          (CategoryTheory.Functor.map_comp
            CompatibleAtlasPresentation.localizationFunctor _ _)))

@[simp]
theorem localizedRecognitionDomainNatIso_hom_app
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    A.localizedRecognitionDomainNatIso.hom.app S =
      (A.localizedRecognitionDomainIso S).hom := rfl

@[simp]
theorem localizedRecognitionDomainNatIso_inv_app
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    A.localizedRecognitionDomainNatIso.inv.app S =
      (A.localizedRecognitionDomainIso S).inv := rfl

/-- The forward comparison induces the identity on the literal subspace. -/
@[simp]
theorem localizedRecognitionDomainIso_hom_space
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    CompatibleAtlasPresentation.localizedSpaceFunctor.map
        (A.localizedRecognitionDomainIso S).hom = 𝟙 (TopCat.of S.carrier) := by
  rw [localizedRecognitionDomainIso_hom,
    CompatibleAtlasPresentation.localizedSpaceFunctor_map]
  rfl

/-- The formal inverse also induces the literal subspace identity. -/
@[simp]
theorem localizedRecognitionDomainIso_inv_space
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    CompatibleAtlasPresentation.localizedSpaceFunctor.map
        (A.localizedRecognitionDomainIso S).inv = 𝟙 (TopCat.of S.carrier) := by
  have h := congrArg
    (CompatibleAtlasPresentation.localizedSpaceFunctor (K := K)).map
    (A.localizedRecognitionDomainIso S).hom_inv_id
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    A.localizedRecognitionDomainIso_hom_space S] at h
  let f : TopCat.of S.carrier ⟶ TopCat.of S.carrier :=
    CompatibleAtlasPresentation.localizedSpaceFunctor.map
      (A.localizedRecognitionDomainIso S).inv
  have hf : (𝟙 (TopCat.of S.carrier)) ≫ f = 𝟙 (TopCat.of S.carrier) := h
  exact (Category.id_comp f).symm.trans hf

/-- The raw domain comparison commutes with the actual ambient inclusions,
 including every original bounded pullback. -/
theorem compatibleRecognitionDomain_inclusion
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    (A.saturationSource.subspaceCompatibleInclusion S.carrier S.is_domain).comp
        A.compatibleToRecognition =
      (A.compatibleDomainToRecognition S).comp
        (A.recognitionTarget.subspaceCompatibleInclusion S.carrier
          (A.recognitionLiftedDomainOrderIso S).is_domain) := by
  refine CompatibleStrongHom.ext_of_pullback rfl ?_
  intro c
  obtain ⟨d, hd⟩ := A.compatibleToRecognition_hasDomainTargets S.carrier c
  have hc : (A.saturationSource.subspaceCompatibleInclusion S.carrier S.is_domain).baseMap ''
      Set.range ((A.saturationSource.subspacePresentation S.carrier S.is_domain).atlas.chart c) ⊆
        Set.range (A.saturationSource.atlas.chart c.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hfd : (A.compatibleDomainToRecognition S).baseMap ''
      Set.range ((A.saturationSource.subspacePresentation S.carrier S.is_domain).atlas.chart c) ⊆
        Set.range ((A.recognitionTarget.subspacePresentation S.carrier
          (A.recognitionLiftedDomainOrderIso S).is_domain).atlas.chart d) :=
    (A.compatibleToRecognition.toStrongHom.domainBaseMap_admissible_iff
      S.carrier S.carrier
      (by change id '' S.carrier ⊆ S.carrier; rw [Set.image_id]) c d).mpr hd
  have hdd : (A.recognitionTarget.subspaceCompatibleInclusion S.carrier
      (A.recognitionLiftedDomainOrderIso S).is_domain).baseMap ''
        Set.range ((A.recognitionTarget.subspacePresentation S.carrier
          (A.recognitionLiftedDomainOrderIso S).is_domain).atlas.chart d) ⊆
            Set.range (A.recognitionTarget.atlas.chart d.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hfinal :=
    (A.saturationSource.subspaceCompatibleInclusion S.carrier S.is_domain).toStrongHom.comp_admissible
      A.compatibleToRecognition.toStrongHom c c.val d.val hc hd
  refine ⟨d.val, hfinal, ?_⟩
  have hleft := CompatibleStrongHom.comp_pullback
    (A.saturationSource.subspaceCompatibleInclusion S.carrier S.is_domain)
    A.compatibleToRecognition c c.val d.val hc hd hfinal
  have hright := CompatibleStrongHom.comp_pullback
    (A.compatibleDomainToRecognition S)
    (A.recognitionTarget.subspaceCompatibleInclusion S.carrier
      (A.recognitionLiftedDomainOrderIso S).is_domain) c d d.val hfd hdd hfinal
  refine hleft.trans (Eq.trans ?_ hright.symm)
  change (A.saturationSource.atlas.restriction c.val c.val Subset.rfl).comp
      (A.compatibleToRecognition.pullback c.val d.val hd) =
    (A.compatibleToRecognition.pullback c.val d.val hd).comp
      (A.recognitionTarget.atlas.restriction d.val d.val Subset.rfl)
  let q := A.compatibleToRecognition.pullback c.val d.val hd
  have hsrc := congrArg
    (fun r : BoundedAlgHom K (A.saturationSource.atlas.algebra c.val)
      (A.saturationSource.atlas.algebra c.val) => r.comp q)
    (A.saturationSource.atlas.restriction_id c.val Subset.rfl)
  have htgt := congrArg
    (fun r : BoundedAlgHom K (A.recognitionTarget.atlas.algebra d.val)
      (A.recognitionTarget.atlas.algebra d.val) => q.comp r)
    (A.recognitionTarget.atlas.restriction_id d.val Subset.rfl)
  exact hsrc.trans ((BoundedAlgHom.id_comp q).trans
    ((BoundedAlgHom.comp_id q).symm.trans htgt.symm))

/-- The natural domain isomorphisms respect the previously constructed
 ambient recognition isomorphism and canonical domain inclusions. -/
theorem localizedRecognitionDomain_inclusion
    (S : A.saturationSource.atlas.OriginalChartDomain) :
    CompatibleAtlasPresentation.localizationFunctor.map
        (A.saturationSource.subspaceCompatibleInclusion S.carrier S.is_domain) ≫
          A.localizedRecognitionIso.hom =
      (A.localizedRecognitionDomainIso S).hom ≫
        CompatibleAtlasPresentation.localizationFunctor.map
          (A.recognitionTarget.subspaceCompatibleInclusion S.carrier
            (A.recognitionLiftedDomainOrderIso S).is_domain) :=
  (CategoryTheory.Functor.map_comp
    CompatibleAtlasPresentation.localizationFunctor _ _).symm.trans
    ((congrArg CompatibleAtlasPresentation.localizationFunctor.map
      (A.compatibleRecognitionDomain_inclusion S)).trans
        (CategoryTheory.Functor.map_comp
          CompatibleAtlasPresentation.localizationFunctor _ _))

end AffinoidAtlasPresentation
end Langlands.Analytic
