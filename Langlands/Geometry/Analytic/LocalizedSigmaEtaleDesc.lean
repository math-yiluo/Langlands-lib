import Langlands.Geometry.Analytic.DisjointUnionDomainEmbeddings
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.StrongIsoQuasiIso

/-! # Étale morphisms out of disjoint unions of analytic spaces -/

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.AtlasDisjointUnion

open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I : Type z} (A : I → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hA : ∀ i, (A i).atlas.HasNonemptyCharts)

/-- All-pieces étaleness at a point of a component descends from the restriction of a map
to that component. -/
theorem isEtaleAtAllPieces_of_compatibleInclusion_comp
    {C : AffinoidAtlasPresentation.{u, max z v, max z w} K}
    (g : StrongHom (presentation A hA).saturatedPresentation C.saturatedPresentation)
    (i : I) (x : (A i).space)
    (hg : ((compatibleInclusion A hA i).saturationExtension.saturatedComp g
      (A i).atlas.saturatedAtlas_hasAllLocalDomains
      (presentation A hA).atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAtAllPieces x) :
    g.IsEtaleAtAllPieces ⟨i, x⟩ :=
  StrongHom.IsDomainEmbedding.IsEtaleAtAllPieces.of_precomp_domainEmbedding
    (isDomainEmbedding_inclusionStrong A hA i) (compatibleInclusion A hA i).coherent
    (IsOpenEmbedding.sigmaMk : IsOpenEmbedding (@Sigma.mk I (fun j => (A j).space) i)) hg

end Langlands.Analytic.AtlasDisjointUnion

namespace Langlands.Analytic.SaturatedAtlasPresentation

open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {J : Type z}

/-- A strong map out of the chosen disjoint union of saturated presentations is étale once its
restriction to every component is étale. -/
theorem strongEtale_of_sigmaCofan_inj
    (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K)
    {B : SaturatedAtlasPresentation.{u, max z v, max z v} K} (h : sigmaPresentation T ⟶ B)
    (hh : ∀ j, strongEtale ((sigmaCofan T).inj j ≫ h)) : strongEtale h := by
  have hq : (saturationFunctorIso B).inv.IsQuasiIso := isQuasiIso_of_isIso _
  refine (strongEtale_postcomp_quasiIso_iff hq).mp ?_
  refine (strongEtale_ofSaturation_iff (P := AtlasDisjointUnion.presentation (nonemptyFamily T)
    (nonemptyFamily_hasNonemptyCharts T)) (Q := B.presentation)
    (h ≫ (saturationFunctorIso B).inv)).mpr ?_
  rintro ⟨j, x⟩
  have hj : strongEtale ((sigmaCofan T).inj j ≫ h ≫ (saturationFunctorIso B).inv) := by
    convert (strongEtale_postcomp_quasiIso_iff hq).mpr (hh j) using 1
    exact (Category.assoc _ _ _).symm
  have hj' := (strongEtale_ofSaturation_iff (P := nonemptyFamily T j) (Q := B.presentation)
    ((sigmaCofan T).inj j ≫ h ≫ (saturationFunctorIso B).inv)).mp hj
  exact AtlasDisjointUnion.isEtaleAtAllPieces_of_compatibleInclusion_comp (nonemptyFamily T)
    (nonemptyFamily_hasNonemptyCharts T) _ j x (hj' x)

/-- A morphism out of a disjoint union of analytic spaces whose restriction to every piece is
étale is étale. -/
theorem etale_sigmaDesc (Y : J → LocalizedCategory.{u, max z v, max z v} (K := K))
    {Z : LocalizedCategory.{u, max z v, max z v} (K := K)} (f : ∀ j, Y j ⟶ Z)
    (hf : ∀ j, etale (f j)) :
    etale (Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f) := by
  let T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K :=
    fun j => localizedObjectEquiv.symm (Y j)
  let R := rightFractionCoproducts K J
  let φ : ∀ j, localizationFunctor.obj (R.replace (T j)) ⟶ Z :=
    fun j => localizationFunctor.map (R.π (T j)) ≫ f j
  change etale (R.localizedDesc T φ)
  rw [Langlands.CategoryTheory.RightFractionCoproducts.localizedDesc]
  refine etale_comp (etale_of_isIso _) (etale_comp ?_ (etale_of_isIso _))
  rw [etale_localizationFunctor_map_iff_strongEtale]
  refine strongEtale_of_sigmaCofan_inj (R.descSource T φ) _ fun j => ?_
  have hfac : (sigmaCofan (R.descSource T φ)).inj j ≫ R.descNumerator T φ =
      R.π _ ≫ (Langlands.CategoryTheory.RightFractionCoproducts.fraction
        quasiIsomorphisms localizationFunctor (φ j)).f :=
    Cofan.IsColimit.fac _ _ j
  rw [hfac]
  refine (strongEtale_precomp_quasiIso_iff
    (isQuasiIso_nonemptyReplacementHom (R.descSource T φ j))).mpr ?_
  rw [← etale_localizationFunctor_map_iff_strongEtale]
  set fr := Langlands.CategoryTheory.RightFractionCoproducts.fraction
    quasiIsomorphisms localizationFunctor (φ j) with hfr
  have e2 := Langlands.CategoryTheory.RightFractionCoproducts.fraction_spec
    quasiIsomorphisms localizationFunctor (φ j)
  rw [MorphismProperty.RightFraction.map] at e2
  have : IsIso (localizationFunctor.map fr.s) :=
    Localization.inverts localizationFunctor quasiIsomorphisms _ fr.hs
  have key : localizationFunctor.map fr.f = localizationFunctor.map fr.s ≫ φ j ≫
      (localizationFunctor.objObjPreimageIso Z).inv := by
    rw [← hfr] at e2
    rw [e2, IsIso.hom_inv_id_assoc]
  have : IsIso (localizationFunctor.map (R.π (T j))) :=
    Localization.inverts localizationFunctor quasiIsomorphisms _ (R.π_mem _)
  rw [key]
  exact etale_comp (etale_of_isIso _)
    (etale_comp (etale_comp (etale_of_isIso _) (hf j)) (etale_of_isIso _))

end Langlands.Analytic.SaturatedAtlasPresentation
