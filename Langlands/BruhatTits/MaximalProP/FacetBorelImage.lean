import Langlands.BruhatTits.MaximalProP.FacetQuotientTorus
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Absolute.SolvableQuotientExtension
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.HomImage
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Borel images of chamber model morphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {A P H : GroupScheme (Spec (CommRingCat.of k))}

/-- Solvability passes to a scheme-surjective homomorphic image locally of finite type. -/
theorem IsSolvableGroupScheme.map_of_surjective
    (hA : IsSolvableGroupScheme A) (q : A ⟶ H)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left] :
    IsSolvableGroupScheme H := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : LocallyOfFiniteType (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) b q.hom.hom inferInstance
  have : Surjective (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : Group.IsSolvable
      ↑((yonedaGrp.obj (B.obj A)).obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))) := hA
  exact Group.isSolvable_of_surjective (rationalPoints_surjective (B.map q))

/-- A solvable parabolic in a smooth connected affine group is a geometric Borel. -/
theorem IsParabolicSubgroup.isGeometricBorelSubgroup_of_isSolvable
    [IsAffineHom H.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left]
    {i : P ⟶ H} (hi : IsParabolicSubgroup i)
    (hP : IsSolvableGroupScheme P) : IsGeometricBorelSubgroup i := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth P.X.hom := hi.smooth
  have : ConnectedSpace P.X.left := hi.connectedSpace
  obtain ⟨C, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup
  have : IsIso f := hj.maximal (B.obj P) (B.map i) f
    (hi.isClosedSubgroup.baseChange b)
    (inferInstanceAs (Smooth (pullback.snd P.X.hom b)))
    (P.connectedSpace_baseChange_of_smooth_affine b)
    (solvableFieldExtensionStatement k (AlgebraicClosure k) b P hi.smooth hP) hf
  have hgeom : IsBorelSubgroup (B.map i) := by
    have he : (asIso f).inv ≫ j = B.map i := by
      rw [← hf]
      exact Iso.inv_hom_id_assoc (asIso f) (B.map i)
    rw [← he]
    exact hj.iso_comp (asIso f).symm
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hgeom hi.isClosedSubgroup

/-- An inclusion between two Borel subgroup functors is equality. -/
theorem IsBorelSubgroup.range_eq_of_range_le
    {i : A ⟶ H} {j : P ⟶ H}
    (hi : IsBorelSubgroup i) (hj : IsBorelSubgroup j)
    (hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE hle
  have hf : f ≫ j = i := SubgroupFunctor.factorOfRangeLE_comp hle
  have : IsIso f := hi.maximal P j f hj.isClosedSubgroup hj.smooth
    hj.connectedSpace hj.isSolvableGroupScheme hf
  calc
    SubgroupFunctor.range i = SubgroupFunctor.range (f ≫ j) := congrArg _ hf.symm
    _ = SubgroupFunctor.range j := SubgroupFunctor.range_iso_comp (asIso f) j

end Langlands.GroupScheme

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance facetBorelNeutralAffine
    (M : RelativeComponentModelData 𝒪[F] F G) :
    IsAffineHom M.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd M.neutral.group.X.hom
    (IntegralModel.residueBaseMap ↥𝒪[F]))
  infer_instance

/-- The neutral special fibre of a chamber model is solvable. -/
theorem chamberNeutralSpecialFibre_isSolvable
    (hD : D.SatisfiesGroupAxioms)
    (Fc : BuildingFacet D.base.toValuationBuildingData)
    (hFc : D.base.IsChamber Fc.val) :
    IsSolvableGroupScheme (D.models.facetModels.model Fc).neutral.specialFibre := by
  let Q := D.quotients.quotient Fc
  have hQ := hD.reductiveQuotients.facets.reductive_quotients Fc
  have : IsClosedImmersion Q.radicalInclusion.hom.hom.left :=
    hQ.1.isClosedSubgroup
  have : IsAffineHom Q.radical.X.hom := by
    rw [← Over.w Q.radicalInclusion.hom.hom]
    infer_instance
  have : Smooth Q.radical.X.hom := hQ.1.smooth
  have := ((facetQuotient_isTorus_iff_isChamber hD Fc).mpr hFc).isCommMonObj
  exact isSolvableGroupScheme_of_unipotent_fppfQuotient hQ.1.isUnipotent hQ.2.1
    (isSolvableGroupScheme_of_isCommMonObj Q.quotient)

/-- The actual parabolic image in the lower facet's quotient is Borel
when the source facet is a chamber. -/
theorem reductiveImage_isGeometricBorel_of_isChamber
    (hD : D.SatisfiesGroupAxioms)
    (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb)
    (hFb : D.base.IsChamber Fb.val) :
    IsGeometricBorelSubgroup
      ((D.models.facetModels.morphism Fa Fb h).reductiveImageInclusion
        (D.quotients.quotient Fa)) := by
  let φ := D.models.facetModels.morphism Fa Fb h
  let Q := D.quotients.quotient Fa
  let f := φ.neutralSpecialFibreMap ≫ Q.projection
  have hQ := (hD.reductiveQuotients.facets.reductive_quotients Fa).2.2
  have : Smooth Q.quotient.X.hom := hQ.smooth
  have : ConnectedSpace Q.quotient.X.left := hQ.connectedSpace
  have hclosed : IsClosedSubgroup (SchematicImage.inclusion f) :=
    HomImage.isClosedSubgroup_inclusion f
  have hpar : IsParabolicSubgroup (SchematicImage.inclusion f) := by
    obtain ⟨P, i, hi, he⟩ :=
      (hD.reductiveQuotients.facets.parabolic_order Fa).isParabolic ⟨Fb, h⟩
    exact hi.of_range_eq hclosed he
  have : Smooth (D.models.facetModels.model Fb).neutral.group.X.hom :=
    (D.models.facetModels.model Fb).neutral_smooth
  have : Smooth (D.models.facetModels.model Fb).neutral.specialFibre.X.hom :=
    inferInstanceAs (Smooth (pullback.snd
      (D.models.facetModels.model Fb).neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F])))
  have : GeometricallyReduced
      (D.models.facetModels.model Fb).neutral.specialFibre.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
  have : Smooth (SchematicImage.image f).X.hom := hpar.smooth
  have : ConnectedSpace (SchematicImage.image f).X.left := hpar.connectedSpace
  have : GeometricallyIntegral (SchematicImage.image f).X.hom :=
    smoothConnectedAffineGeometry.1 𝓀[F] (SchematicImage.image f)
      inferInstance inferInstance inferInstance
  let : Subsingleton (Spec (CommRingCat.of 𝓀[F])) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum 𝓀[F]))
  have : IrreducibleSpace (SchematicImage.image f).X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (SchematicImage.image f).X.hom
  have : Flat (SchematicImage.projection f).hom.hom.left :=
    HomImage.flat_projection f
  have : Surjective (SchematicImage.projection f).hom.hom.left :=
    DominantHomFlat.surjective_of_flat (SchematicImage.projection f)
  have hsol := (chamberNeutralSpecialFibre_isSolvable hD Fb hFb).map_of_surjective
    (SchematicImage.projection f)
  exact hpar.isGeometricBorelSubgroup_of_isSolvable hsol

/-- The actual reductive image is a geometric Borel precisely for chambers. -/
theorem reductiveImage_isGeometricBorel_iff_isChamber
    (hD : D.SatisfiesGroupAxioms)
    (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb) :
    IsGeometricBorelSubgroup
      ((D.models.facetModels.morphism Fa Fb h).reductiveImageInclusion
        (D.quotients.quotient Fa)) ↔
      D.base.IsChamber Fb.val := by
  refine ⟨?_, reductiveImage_isGeometricBorel_of_isChamber hD Fa Fb h⟩
  intro hB
  have hex := h
  obtain ⟨g, Aa, Ab, hab, ha, hb⟩ := hex
  have hAb : AffineRootSystem.IsFacet D.base.affineRoots Ab := by
    obtain ⟨b, hb', -⟩ := hab.2
    exact ⟨b, hb'⟩
  obtain ⟨Ac, hc, hbc⟩ := hAb.exists_isChamber_isFaceOf
    hD.affineRootSystem.apartmentAxioms.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  let Cc : BuildingFacet D.base.toValuationBuildingData :=
    ⟨D.base.translatedApartmentMap g '' Ac, g, Ac, hc.isFacet, rfl⟩
  have hCc : D.base.IsChamber Cc.val := ⟨g, Ac, hc, rfl⟩
  have hac : FacetPrecedes D.base.toValuationBuildingData Fa Cc :=
    ⟨g, Aa, Ac, hab.trans hbc, ha, rfl⟩
  have hbc' : FacetPrecedes D.base.toValuationBuildingData Fb Cc :=
    ⟨g, Ab, Ac, hbc, hb, rfl⟩
  let Ib : IncidentFacets D.base.toValuationBuildingData Fa := ⟨Fb, h⟩
  let Ic : IncidentFacets D.base.toValuationBuildingData Fa := ⟨Cc, hac⟩
  have horder := hD.reductiveQuotients.facets.parabolic_order Fa
  have hle := horder.order_preserving Ib Ic hbc'
  have hC := reductiveImage_isGeometricBorel_of_isChamber hD Fa Cc hac hCc
  have he :
      D.models.facetModels.incidentParabolicImage Fa (D.quotients.quotient Fa) Ic =
      D.models.facetModels.incidentParabolicImage Fa (D.quotients.quotient Fa) Ib :=
    hC.isBorelSubgroup.range_eq_of_range_le hB.isBorelSubgroup hle
  have hI : Ic = Ib := horder.injective he
  have hfacet : Cc = Fb := congrArg Subtype.val hI
  simpa only [← hfacet] using hCc

/-- The actual chamber-image inclusion, together with its geometric Borel property. -/
def chamberBorelImageInclusion
    (hD : D.SatisfiesGroupAxioms)
    (Fa Fc : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fc)
    (hFc : D.base.IsChamber Fc.val) :
    {i : (D.models.facetModels.morphism Fa Fc h).reductiveImage
        (D.quotients.quotient Fa) ⟶ (D.quotients.quotient Fa).quotient //
      IsGeometricBorelSubgroup i} :=
  ⟨(D.models.facetModels.morphism Fa Fc h).reductiveImageInclusion
      (D.quotients.quotient Fa),
    reductiveImage_isGeometricBorel_of_isChamber hD Fa Fc h hFc⟩

end Langlands.BruhatTits.MaximalProP
