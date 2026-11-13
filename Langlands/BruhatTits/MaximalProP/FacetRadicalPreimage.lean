import Langlands.BruhatTits.MaximalProP.FacetBorelImage
import Langlands.GroupScheme.Reductive.ParabolicUnipotentKernel
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.HomogeneousQuotientRationalPoints
import Langlands.GroupScheme.FiniteFieldTorsorPointProof

/-! # Radical preimages for the actual incident facet morphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {A B Q U : GroupScheme (Spec (CommRingCat.of k))}

/-- After a map with unipotent kernel and parabolic image, quotienting by
the ambient radical still gives a smooth connected unipotent image kernel. -/
theorem HasSmoothConnectedUnipotentKernel.schematicImage_comp
    [IsAffineHom A.X.hom] [Smooth A.X.hom] [ConnectedSpace A.X.left]
    [IsAffineHom B.X.hom] [Smooth B.X.hom] [ConnectedSpace B.X.left]
    [IsAffineHom Q.X.hom]
    (f : A ⟶ B) (q : B ⟶ Q) (n : U ⟶ B)
    (hf : HasSmoothConnectedUnipotentKernel f)
    (hp : IsParabolicSubgroup (SchematicImage.inclusion f))
    (hn : IsUnipotentRadical n)
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n) :
    HasSmoothConnectedUnipotentKernel (SchematicImage.projection (f ≫ q)) := by
  have : GeometricallyIntegral A.X.hom :=
    smoothConnectedAffineGeometry.1 k A inferInstance inferInstance inferInstance
  have : Mono (SchematicImage.inclusion f).hom.hom :=
    (HomImage.isClosedSubgroup_inclusion f).mono_overHom
  have : Flat (SchematicImage.projection f).hom.hom.left :=
    HomImage.flat_projection f
  have : Surjective (SchematicImage.projection f).hom.hom.left :=
    HomImage.surjective_projection f
  have : LocallyOfFinitePresentation (SchematicImage.projection f).hom.hom.left :=
    HomImage.locallyOfFinitePresentation_projection f
  have hfirst : HasSmoothConnectedUnipotentKernel (SchematicImage.projection f) :=
    .of_comp_mono (SchematicImage.projection f) (SchematicImage.inclusion f)
      (by simpa only [SchematicImage.projection_inclusion] using hf)
  have hsecond :=
    hp.hasSmoothConnectedUnipotentKernel_comp (SchematicImage.inclusion f) n hn q hk
  have hcomp : HasSmoothConnectedUnipotentKernel (f ≫ q) := by
    simpa only [← Category.assoc, SchematicImage.projection_inclusion] using
      (HasSmoothConnectedUnipotentKernel.comp (SchematicImage.projection f)
        (SchematicImage.inclusion f ≫ q) hfirst hsecond)
  have : Mono (SchematicImage.inclusion (f ≫ q)).hom.hom :=
    (HomImage.isClosedSubgroup_inclusion (f ≫ q)).mono_overHom
  exact .of_comp_mono (SchematicImage.projection (f ≫ q))
    (SchematicImage.inclusion (f ≫ q))
    (by simpa only [SchematicImage.projection_inclusion] using hcomp)

/-- Over a finite field, an fppf homomorphism with smooth connected actual
kernel is surjective on rational points. -/
theorem HasSmoothConnectedUnipotentKernel.rationalPoints_surjective
    [Finite k] [IsAffineHom A.X.hom] [IsAffineHom Q.X.hom]
    (q : A ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q) :
    Function.Surjective (rationalPoints.map q) := by
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have : Smooth (kernel q).X.hom := hq.1
  have hquot : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q :=
    ⟨inferInstance, inferInstance, inferInstance, rfl⟩
  have hz : (SubgroupFunctor.range (kernelι q)).IsRepresentedBy (kernelι q) :=
    ⟨inferInstance, rfl⟩
  exact HomogeneousQuotient.rational_lifts_of_finite_torsor_identity k A (kernel q)
    (kernelι q) q.hom.hom (fun T g h => hquot.fibers_iff hz T g h)
    finiteFieldTorsorPointStatement hq.2.1

end Langlands.GroupScheme

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance facetRadicalNeutralAffine
    (M : RelativeComponentModelData 𝒪[F] F G) :
    IsAffineHom M.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd M.neutral.group.X.hom
    (IntegralModel.residueBaseMap ↥𝒪[F]))
  infer_instance

local instance facetRadicalNeutralSmooth
    (M : RelativeComponentModelData 𝒪[F] F G) :
    Smooth M.neutral.specialFibre.X.hom := by
  have : Smooth M.neutral.group.X.hom := M.neutral_smooth
  change Smooth (pullback.snd M.neutral.group.X.hom
    (IntegralModel.residueBaseMap ↥𝒪[F]))
  infer_instance

local instance facetRadicalNeutralConnected
    (M : RelativeComponentModelData 𝒪[F] F G) :
    ConnectedSpace M.neutral.specialFibre.X.left :=
  M.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres M.neutral_connectedFibres

/-- The actual projection from the upper neutral special fibre to its
image in the lower reductive quotient has smooth connected unipotent kernel. -/
theorem facetReductiveImageProjection_kernel
    (hD : D.SatisfiesGroupAxioms)
    (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb) :
    HasSmoothConnectedUnipotentKernel
      (SchematicImage.projection
        ((D.models.facetModels.morphism Fa Fb h).neutralSpecialFibreMap ≫
          (D.quotients.quotient Fa).projection)) := by
  let φ := D.models.facetModels.morphism Fa Fb h
  let Q := D.quotients.quotient Fa
  have hQ := hD.reductiveQuotients.facets.reductive_quotients Fa
  have hgen : D.models.SatisfiesGeneralMorphismAxioms := hD.reductiveQuotients.1
  have hf : HasSmoothConnectedUnipotentKernel φ.neutralSpecialFibreMap :=
    (hgen (BuildingModelIndex.ofFacet Fa)
      (BuildingModelIndex.ofFacet Fb) (Or.inr ⟨Fa, Fb, rfl, rfl, h⟩)).2
  exact hf.schematicImage_comp φ.neutralSpecialFibreMap Q.projection
    Q.radicalInclusion (hD.reductiveQuotients.facets.parabolic_images Fa Fb h)
    hQ.1 hQ.2.1.2.2.2

/-- The radical of the actual incident reductive image has precisely the
upper facet's positive subgroup as its lower parahoric preimage. -/
theorem facetReductiveImage_radicalPreimage
    (hD : D.SatisfiesGroupAxioms)
    (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb)
    (U : GroupScheme (Spec (CommRingCat.of 𝓀[F])))
    (j : U ⟶ (D.models.facetModels.morphism Fa Fb h).reductiveImage
      (D.quotients.quotient Fa))
    (hj : IsUnipotentRadical j) :
    (((rationalPoints.map
        (j ≫ (D.models.facetModels.morphism Fa Fb h).reductiveImageInclusion
          (D.quotients.quotient Fa))).range.comap
        (D.quotients.quotient Fa).parahoricReduction).map
      (D.models.facetModels.model Fa).neutral.integralPoints.subtype) =
      (D.quotients.quotient Fb).positivePoints := by
  let Ma := D.models.facetModels.model Fa
  let Mb := D.models.facetModels.model Fb
  let φ := D.models.facetModels.morphism Fa Fb h
  let Qa := D.quotients.quotient Fa
  let Qb := D.quotients.quotient Fb
  let f := φ.neutralSpecialFibreMap ≫ Qa.projection
  let p := SchematicImage.projection f
  let i := SchematicImage.inclusion f
  have hQa : Qa.IsReductiveQuotient :=
    hD.reductiveQuotients.facets.reductive_quotients Fa
  have hQb : Qb.IsReductiveQuotient :=
    hD.reductiveQuotients.facets.reductive_quotients Fb
  have hpos := hD.reductiveQuotients.facets.positive_radicals Fa Fb h
  have : Smooth Qa.quotient.X.hom := hQa.2.2.smooth
  have : GeometricallyIntegral Mb.neutral.specialFibre.X.hom :=
    smoothConnectedAffineGeometry.1 𝓀[F] Mb.neutral.specialFibre
      inferInstance inferInstance inferInstance
  have : Flat p.hom.hom.left := HomImage.flat_projection f
  have : Surjective p.hom.hom.left := HomImage.surjective_projection f
  have : LocallyOfFinitePresentation p.hom.hom.left :=
    HomImage.locallyOfFinitePresentation_projection f
  have hp : HasSmoothConnectedUnipotentKernel p :=
    facetReductiveImageProjection_kernel hD Fa Fb h
  have hr := hp.radical_comap_eq hQb.1 hj
  have hmem (x : rationalPoints Mb.neutral.specialFibre) :
      rationalPoints.map p x ∈ (rationalPoints.map j).range ↔
        x ∈ Qb.radicalPoints := by
    change x ∈ ((SubgroupFunctor.range j).comap p).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of 𝓀[F])))) ↔
      x ∈ (SubgroupFunctor.range Qb.radicalInclusion).carrier _
    rw [hr]
  have hcomp (x : rationalPoints Mb.neutral.specialFibre) :
      rationalPoints.map i (rationalPoints.map p x) =
        Qa.projectionPoints (rationalPoints.map φ.neutralSpecialFibreMap x) := by
    change (x ≫ p.hom.hom) ≫ i.hom.hom =
      (x ≫ φ.neutralSpecialFibreMap.hom.hom) ≫ Qa.projection.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom,
      SchematicImage.projection_inclusion, Grp.comp_hom_hom, ← Category.assoc]
  apply le_antisymm
  · rintro g ⟨a, ha, rfl⟩
    obtain ⟨t, rfl⟩ := Ma.neutralSectionsEquiv.surjective a
    obtain ⟨u, hu⟩ := ha
    obtain ⟨x, hx⟩ := hp.rationalPoints_surjective p (rationalPoints.map j u)
    obtain ⟨s, hs⟩ := hpos.2.1 x
    have hsrad : Mb.neutral.reduction s ∈ Qb.radicalPoints :=
      (hmem _).mp ⟨u, by rw [hs, hx]⟩
    have hspos : Mb.neutral.integralPointMap s ∈ Qb.positivePoints :=
      ⟨s, hsrad, rfl⟩
    have hred : Qa.reductiveReduction t =
        Qa.reductiveReduction (rationalPoints.map φ.neutral.hom s) := by
      rw [SpecialFibreQuotientData.parahoricReduction_neutralSectionsEquiv] at hu
      change rationalPoints.map (j ≫ i) u = Qa.reductiveReduction t at hu
      rw [← hu]
      change rationalPoints.map i (rationalPoints.map j u) = _
      rw [← hx, ← hs, hcomp]
      exact (congrArg Qa.projectionPoints (φ.neutral_reduction_naturality s)).symm
    have hdiff : t * (rationalPoints.map φ.neutral.hom s)⁻¹ ∈ Qa.positiveSections := by
      rw [← Qa.ker_reductiveReduction hQa.2.1, MonoidHom.mem_ker,
        map_mul, map_inv, hred, mul_inv_cancel]
    have hdiffpos :
        Ma.neutral.integralPointMap t * (Mb.neutral.integralPointMap s)⁻¹ ∈
          Qb.positivePoints := by
      apply hpos.2.2
      refine ⟨t * (rationalPoints.map φ.neutral.hom s)⁻¹, hdiff, ?_⟩
      rw [map_mul, map_inv, φ.neutral_integralPointMap]
    change Ma.neutral.integralPointMap t ∈ Qb.positivePoints
    simpa only [inv_mul_cancel_right] using Qb.positivePoints.mul_mem hdiffpos hspos
  · rintro g ⟨s, hs, rfl⟩
    refine ⟨Ma.neutralSectionsEquiv (rationalPoints.map φ.neutral.hom s), ?_, ?_⟩
    · obtain ⟨u, hu⟩ := (hmem _).mpr hs
      refine ⟨u, ?_⟩
      rw [SpecialFibreQuotientData.parahoricReduction_neutralSectionsEquiv]
      change rationalPoints.map i (rationalPoints.map j u) = _
      rw [hu, hcomp]
      exact (congrArg Qa.projectionPoints (φ.neutral_reduction_naturality s)).symm
    · exact φ.neutral_integralPointMap s

/-- Retain the literal lower-parahoric radical preimage in the original
rational group, with its proved equality to the upper positive subgroup. -/
def incidentRadicalPreimageSubgroup
    (hD : D.SatisfiesGroupAxioms)
    (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb)
    (U : GroupScheme (Spec (CommRingCat.of 𝓀[F])))
    (j : U ⟶ (D.models.facetModels.morphism Fa Fb h).reductiveImage
      (D.quotients.quotient Fa))
    (hj : IsUnipotentRadical j) :
    {H : Subgroup (rationalPoints G) //
      H = (D.quotients.quotient Fb).positivePoints} :=
  ⟨(((rationalPoints.map
      (j ≫ (D.models.facetModels.morphism Fa Fb h).reductiveImageInclusion
        (D.quotients.quotient Fa))).range.comap
      (D.quotients.quotient Fa).parahoricReduction).map
    (D.models.facetModels.model Fa).neutral.integralPoints.subtype),
    facetReductiveImage_radicalPreimage hD Fa Fb h U j hj⟩

/-- All three comparisons use the original models, quotients and images
under the single-group axioms alone. -/
theorem facetReductiveComparisons (hD : D.SatisfiesGroupAxioms) :
    FacetReductiveComparisons D :=
  ⟨facetQuotient_isTorus_iff_isChamber hD,
    reductiveImage_isGeometricBorel_iff_isChamber hD,
    facetReductiveImage_radicalPreimage hD⟩

/-- The exact published facet-comparison statement at arbitrary universe. -/
theorem facetReductiveComparisonStatement :
    FacetReductiveComparisonStatement.{u} := by
  intro F _ _ _ _ G _ D hD
  exact facetReductiveComparisons hD

end Langlands.BruhatTits.MaximalProP
