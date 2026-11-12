import Langlands.BruhatTits.IntegralModels.Transport.Package
import Langlands.BruhatTits.IntegralModels.Transport.RootReflection

/-! # Transport of KP model families along a building transport package

Given `T : BuildingTransportPackage B B' f`, the model at an index `Ω` of `B'` is the
transport along `f` of the model at `Φ⁻¹ Ω`; morphisms, tori over translated charts and
facet quotients are carried in the same way. KP Axioms 4.1.20 and 4.1.22 transfer, with the
root datum transported along `σ` and `f`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {B : ValuationBuildingData G} {B' : ValuationBuildingData H} {f : G ≅ H}
  {R : Type u} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

namespace BuildingTransportPackage

variable (T : BuildingTransportPackage B B' f)

/-- The index of a facet of `B'` corresponds to the index of the corresponding facet of `B`. -/
theorem indexEquiv_symm_ofFacet (F : BuildingFacet B') :
    T.indexEquiv.symm (BuildingModelIndex.ofFacet F) =
      BuildingModelIndex.ofFacet (T.facetEquiv.symm F) :=
  rfl

/-- The one-group fixer of `Φ Ω` is the `f`-image of the one-group fixer of `Ω`. -/
theorem map_oneFixer (Ω : BuildingModelIndex B) :
    (BuildingModelFamily.oneFixer Ω).map (rationalPoints.map f.hom) =
      BuildingModelFamily.oneFixer (T.indexEquiv Ω) := by
  rw [BuildingModelFamily.oneFixer, BuildingModelFamily.oneFixer,
    Subgroup.map_inf_eq _ _ _ (rationalPoints_map_injective_of_iso f), T.map_pointwiseFixer,
    map_rationalCommonNormKernel]
  rfl

/-- The zero-group fixer of `Φ Ω` is the `f`-image of the zero-group fixer of `Ω`, when the
zero subgroups correspond. -/
theorem map_zeroFixer {P : ParahoricBuildingData G} {P' : ParahoricBuildingData H}
    (hzero : P'.zeroSubgroup = P.zeroSubgroup.map (rationalPoints.map f.hom))
    (Ω : BuildingModelIndex B) :
    (BuildingModelFamily.zeroFixer P Ω).map (rationalPoints.map f.hom) =
      BuildingModelFamily.zeroFixer P' (T.indexEquiv Ω) := by
  rw [BuildingModelFamily.zeroFixer, BuildingModelFamily.zeroFixer,
    Subgroup.map_inf_eq _ _ _ (rationalPoints_map_injective_of_iso f), T.map_pointwiseFixer,
    hzero]
  rfl

/-- Facets incident above `F` in `B'` correspond to facets incident above the corresponding
facet of `B`. -/
def incidentEquiv (F : BuildingFacet B') :
    IncidentFacets B' F ≃ IncidentFacets B (T.facetEquiv.symm F) where
  toFun F' := ⟨T.facetEquiv.symm F'.val, T.facetPrecedes_symm F'.property⟩
  invFun F'' := ⟨T.facetEquiv F''.val, by
    have h := T.facetPrecedes_map F''.property
    rwa [Equiv.apply_symm_apply] at h⟩
  left_inv F' := Subtype.ext (Equiv.apply_symm_apply _ _)
  right_inv F'' := Subtype.ext (Equiv.symm_apply_apply _ _)

section Residue

variable [IsLocalRing R]

/-- The Lie-weight sign formula of KP Axiom 4.1.22(3) on a pair of apartment subsets of `B'`
follows from the formula on the corresponding subsets of `B`. -/
theorem hasApartmentLieWeightSignFormula_transport
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target) (Q : SpecialFibreQuotientData target)
    {j : B.S.toGrp ⟶ G} {j' : B'.S.toGrp ⟶ H} (T₀ : IntegralTorusData source B.S j)
    (hj : j ≫ f.hom = CommGroupScheme.groupHom T.σ.hom ≫ j')
    (hT : IsSplitTorus T₀.torus.toGrp) (Fa Fa' : Set B'.Apartment)
    (h : φ.HasApartmentLieWeightSignFormula B Q T₀ hT (T.A.symm '' Fa) (T.A.symm '' Fa')) :
    (φ.transport f).HasApartmentLieWeightSignFormula B' (Q.transport f)
      (T₀.transport f T.σ hj) hT Fa Fa' := by
  intro x hx v hv
  obtain ⟨v₀, rfl⟩ := (RealTorusSpace.cocharacterRealCongr T.σ).surjective v
  have hv₀ : (Submodule.Quotient.mk v₀ : TranslationSpace B.i) +ᵥ T.A.symm x ∈
      T.A.symm '' Fa' := by
    refine ⟨_, hv, ?_⟩
    apply T.A.injective
    rw [AffineEquiv.apply_symm_apply, T.A_mk_vadd, AffineEquiv.apply_symm_apply]
  have key := h _ ⟨x, hx, rfl⟩ v₀ hv₀
  rw [RelativeComponentModelHom.transport_quotientTorusInclusion]
  change nonzeroLieImageWeights (φ.quotientTorusInclusion Q T₀)
      (φ.reductiveImageInclusion Q) = _
  rw [key]
  ext χ
  simp only [IntegralTorusData.transport_characterSpecialization_symm,
    eval_cocharacterRealCongr]
  exact Iff.rfl

/-- The derivative root datum of KP Axiom 4.1.22(6) on an apartment subset of `B'` follows
from the datum on the corresponding subset of `B`, for the transported root datum. -/
theorem hasApartmentDerivativeRootDatum_transport {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) {j : B.S.toGrp ⟶ G} {j' : B'.S.toGrp ⟶ H}
    (T₀ : IntegralTorusData D B.S j)
    (hj : j ≫ f.hom = CommGroupScheme.groupHom T.σ.hom ≫ j')
    (Droot : RelativeRootReflectionData B.i) (hT : IsSplitTorus T₀.torus.toGrp)
    (Fa : Set B'.Apartment)
    (h : HasApartmentDerivativeRootDatum B Q T₀ Droot hT (T.A.symm '' Fa)) :
    HasApartmentDerivativeRootDatum B' (Q.transport f) (T₀.transport f T.σ hj)
      (Droot.transport T.σ f T.comm) hT Fa := by
  obtain ⟨J, hJ, P, hP, hgraph⟩ := h
  refine ⟨J, hJ, P, hP, hgraph.trans ?_⟩
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨relativeRootsTransportEquiv T.σ f T.comm a, ?_, ?_⟩
    · change characterLattice.congr T.σ a.val ∈ facetDerivativeRoots B' Fa
      rw [← T.image_symm_image Fa, T.congr_mem_facetDerivativeRoots_iff]
      exact ha
    · rw [RelativeRootReflectionData.transport_coroot]
      change _ = ((T₀.transport f T.σ hj).characterSpecialization hT
          (characterLattice.congr T.σ a.val), _)
      rw [IntegralTorusData.transport_characterSpecialization,
        IntegralTorusData.transport_cocharacterSpecialization]
  · rintro ⟨a', ha', rfl⟩
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv T.σ f T.comm).surjective a'
    refine ⟨a, ?_, ?_⟩
    · rw [← T.congr_mem_facetDerivativeRoots_iff, T.image_symm_image]
      exact ha'
    · rw [RelativeRootReflectionData.transport_coroot]
      change ((T₀.transport f T.σ hj).characterSpecialization hT
          (characterLattice.congr T.σ a.val), _) = _
      rw [IntegralTorusData.transport_characterSpecialization,
        IntegralTorusData.transport_cocharacterSpecialization]

end Residue
end BuildingTransportPackage

namespace BuildingModelFamily

/-- The model family of `B` carried to `B'`: the model at `Ω` is the transport along `f` of
the model at `Φ⁻¹ Ω`, and the torus over the chart `g · A(S')` is the transport along
`(σ, f)` of the torus over the chart `f⁻¹(g) · A(S)`. -/
def transport (M : BuildingModelFamily B R) (T : BuildingTransportPackage B B' f) :
    BuildingModelFamily B' R where
  model Ω := (M.model (T.indexEquiv.symm Ω)).transport f
  morphism _ _ h := (M.morphism _ _ (T.modelMorphismRequired_symm h)).transport f
  torus Ω g Ωa h :=
    (M.torus (T.indexEquiv.symm Ω) (rationalPoints.map f.inv g) (T.A.symm '' Ωa)
      (T.symm_val_eq h)).transport f T.σ (T.conj_comm g)

variable (M : BuildingModelFamily B R) (T : BuildingTransportPackage B B' f)

theorem transport_model (Ω : BuildingModelIndex B') :
    (M.transport T).model Ω = (M.model (T.indexEquiv.symm Ω)).transport f :=
  rfl

section Residue

variable [IsLocalRing R]

omit [IsLocalRing R] in
/-- Neutral-model isomorphisms of corresponding indices are carried along. -/
theorem neutralModelsIsomorphic_transport {Ω₁ Ω₂ : BuildingModelIndex B'}
    (h : M.NeutralModelsIsomorphic (T.indexEquiv.symm Ω₁) (T.indexEquiv.symm Ω₂)) :
    (M.transport T).NeutralModelsIsomorphic Ω₁ Ω₂ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.transportId f, hφ⟩

variable {M}

/-- KP Axiom 4.1.20 transfers to the transported family, for parahoric data of `H` on `B'`
whose zero subgroup is the `f`-image of that of `P`. -/
theorem modelAxiomClauses_transport {P : ParahoricBuildingData G} (hM : M.ModelAxiomClauses P)
    {P' : ParahoricBuildingData H} (hP' : P'.toValuationBuildingData = B')
    (hzero : P'.zeroSubgroup = P.zeroSubgroup.map (rationalPoints.map f.hom)) :
    (M.transport T).ModelAxiomClauses P' where
  building_eq := hP'
  full_points Ω := by
    refine ((M.model (T.indexEquiv.symm Ω)).transport_full_integralPoints f).trans ?_
    rw [hM.full_points, T.map_oneFixer, Equiv.apply_symm_apply]
  neutral_points Ω := by
    refine ((M.model (T.indexEquiv.symm Ω)).transport_neutral_integralPoints f).trans ?_
    rw [hM.neutral_points, T.map_zeroFixer hzero, Equiv.apply_symm_apply]
  facet_constancy Ω F hsub := by
    obtain ⟨φ, hφ⟩ := hM.facet_constancy (T.indexEquiv.symm Ω) (T.facetEquiv.symm F)
      (Set.image_mono hsub)
    exact ⟨φ.transportId f, hφ⟩
  closure_invariance g Ωa hne hb := by
    apply M.neutralModelsIsomorphic_transport T
    have e₁ : T.indexEquiv.symm (BuildingModelIndex.ofApartment g Ωa hne hb) =
        BuildingModelIndex.ofApartment (rationalPoints.map f.inv g) (T.A.symm '' Ωa)
          (hne.image _) (isBoundedSubset_affineEquiv_image T.A.symm hb) :=
      Subtype.ext (T.symm_image_translated g Ωa)
    have e₂ : T.indexEquiv.symm (BuildingModelIndex.ofApartment g (apartmentClosure B' Ωa)
          (nonempty_apartmentClosure B' hne) (isBoundedSubset_apartmentClosure B' hb)) =
        BuildingModelIndex.ofApartment (rationalPoints.map f.inv g)
          (apartmentClosure B (T.A.symm '' Ωa)) (nonempty_apartmentClosure B (hne.image _))
          (isBoundedSubset_apartmentClosure B
            (isBoundedSubset_affineEquiv_image T.A.symm hb)) := by
      apply Subtype.ext
      change T.Φ.symm '' (B'.translatedApartmentMap g '' apartmentClosure B' Ωa) =
        B.translatedApartmentMap (rationalPoints.map f.inv g) ''
          apartmentClosure B (T.A.symm '' Ωa)
      rw [T.symm_image_translated, image_apartmentClosure]
    rw [e₁, e₂]
    exact hM.closure_invariance _ _ _ _
  torus_clause Ω g Ωa h :=
    (IntegralTorusData.satisfiesTorusClause_transport_iff _ f T.σ (T.conj_comm g)).2
      (hM.torus_clause _ _ _ _)
  simply_connected Ω :=
    (RelativeComponentModelData.hasEqualComponentsForSimplyConnected_transport_iff _ f).2
      (hM.simply_connected _)

/-- KP Axiom 4.1.20 in its packaged form. -/
theorem satisfiesModelAxioms_transport {P : ParahoricBuildingData G}
    (hM : M.SatisfiesModelAxioms P) {P' : ParahoricBuildingData H}
    (hP' : P'.toValuationBuildingData = B')
    (hzero : P'.zeroSubgroup = P.zeroSubgroup.map (rationalPoints.map f.hom)) :
    (M.transport T).SatisfiesModelAxioms P' :=
  modelAxiomClauses_transport T hM hP' hzero

/-- The preamble and part (1) of KP Axiom 4.1.22 transfer. -/
theorem satisfiesGeneralMorphismAxioms_transport (hM : M.SatisfiesGeneralMorphismAxioms) :
    (M.transport T).SatisfiesGeneralMorphismAxioms := fun _ _ h =>
  (RelativeComponentModelHom.satisfiesGeneralSpecialFibreClauses_transport_iff _ f).2
    (hM _ _ (T.modelMorphismRequired_symm h))

end Residue
end BuildingModelFamily

namespace BuildingModelQuotientFamily

variable [IsLocalRing R] {M : BuildingModelFamily B R}

/-- The facet quotients carried to `B'`: the quotient at `F` is that at `Φ⁻¹ F`. -/
def transport (QF : BuildingModelQuotientFamily B M) (T : BuildingTransportPackage B B' f) :
    BuildingModelQuotientFamily B' (M.transport T) where
  quotient F := (QF.quotient (T.facetEquiv.symm F)).transport f

variable {QF : BuildingModelQuotientFamily B M} (T : BuildingTransportPackage B B' f)

variable {Droot : RelativeRootReflectionData B.i} (hQF : QF.FacetAxiomClauses Droot)
include hQF

/-- The quotients of `B'` are maximal reductive quotients. -/
theorem transport_reductive_quotients (F : BuildingFacet B') :
    ((QF.transport T).quotient F).IsReductiveQuotient :=
  (SpecialFibreQuotientData.isReductiveQuotient_transport_iff _ f).2
    (hQF.reductive_quotients (T.facetEquiv.symm F))

/-- KP Axiom 4.1.22(2) on `B'`. -/
theorem transport_parabolic_images (F F' : BuildingFacet B') (h : FacetPrecedes B' F F') :
    ((M.transport T).facetModels.morphism F F' h).HasParabolicSpecialFibreImage :=
  (RelativeComponentModelHom.hasParabolicSpecialFibreImage_transport_iff _ f).2
    (hQF.parabolic_images _ _ (T.facetPrecedes_symm h))

/-- KP Axiom 4.1.22(3), first paragraph, on `B'`. -/
theorem transport_common_tori (F F' : BuildingFacet B') (h : FacetPrecedes B' F F')
    (g : rationalPoints H) (Fa Fa' : Set B'.Apartment)
    (hface : AffineRootSystem.IsFaceOf B'.affineRoots Fa Fa')
    (hF : F.val = B'.translatedApartmentMap g '' Fa)
    (hF' : F'.val = B'.translatedApartmentMap g '' Fa') :
    ((M.transport T).torus (BuildingModelIndex.ofFacet F') g Fa' hF').IsClosedSplit ∧
      ((M.transport T).facetModels.morphism F F' h).HasMaximalSplitTori
        ((QF.transport T).quotient F)
        ((M.transport T).torus (BuildingModelIndex.ofFacet F') g Fa' hF') := by
  have hface₀ : AffineRootSystem.IsFaceOf B.affineRoots (T.A.symm '' Fa) (T.A.symm '' Fa') := by
    rw [← T.isFaceOf_image_iff, T.image_symm_image, T.image_symm_image]
    exact hface
  have h₀ := hQF.common_tori _ _ (T.facetPrecedes_symm h) (rationalPoints.map f.inv g) _ _
    hface₀ (T.symm_val_eq hF) (T.symm_val_eq hF')
  exact ⟨(IntegralTorusData.isClosedSplit_transport_iff _ f T.σ (T.conj_comm g)).2 h₀.1,
    (RelativeComponentModelHom.hasMaximalSplitTori_transport_iff _ _ _ f T.σ
      (T.conj_comm g)).2 h₀.2⟩

/-- KP Axiom 4.1.22(3), second paragraph, on `B'`. -/
theorem transport_lie_weight_signs (F F' : BuildingFacet B') (h : FacetPrecedes B' F F')
    (g : rationalPoints H) (Fa Fa' : Set B'.Apartment)
    (hface : AffineRootSystem.IsFaceOf B'.affineRoots Fa Fa')
    (hF : F.val = B'.translatedApartmentMap g '' Fa)
    (hF' : F'.val = B'.translatedApartmentMap g '' Fa')
    (hT : IsSplitTorus
      ((M.transport T).torus (BuildingModelIndex.ofFacet F') g Fa' hF').torus.toGrp) :
    ((M.transport T).facetModels.morphism F F' h).HasApartmentLieWeightSignFormula
      B' ((QF.transport T).quotient F)
      ((M.transport T).torus (BuildingModelIndex.ofFacet F') g Fa' hF') hT Fa Fa' := by
  have hface₀ : AffineRootSystem.IsFaceOf B.affineRoots (T.A.symm '' Fa) (T.A.symm '' Fa') := by
    rw [← T.isFaceOf_image_iff, T.image_symm_image, T.image_symm_image]
    exact hface
  exact T.hasApartmentLieWeightSignFormula_transport _ _ _ (T.conj_comm g) hT Fa Fa'
    (hQF.lie_weight_signs _ _ (T.facetPrecedes_symm h) (rationalPoints.map f.inv g) _ _
      hface₀ (T.symm_val_eq hF) (T.symm_val_eq hF') hT)

/-- KP Axiom 4.1.22(4) on `B'`. -/
theorem transport_reduction_preimages (F F' : BuildingFacet B') (h : FacetPrecedes B' F F') :
    ((M.transport T).facetModels.morphism F F' h).HasParabolicReductionPreimage :=
  (RelativeComponentModelHom.hasParabolicReductionPreimage_transport_iff _ f).2
    (hQF.reduction_preimages _ _ (T.facetPrecedes_symm h))

omit hQF [IsLocalRing R] in
/-- The facet-model morphisms of `B'` are the transports of those of `B`. -/
theorem transport_facetModels_morphism (F F' : BuildingFacet B') (h : FacetPrecedes B' F F') :
    (M.transport T).facetModels.morphism F F' h =
      (M.facetModels.morphism (T.facetEquiv.symm F) (T.facetEquiv.symm F')
        (T.facetPrecedes_symm h)).transport f :=
  rfl

omit hQF in
/-- The parabolic image of an incident facet of `B'` is that of the corresponding incident
facet of `B`. -/
theorem transport_incidentParabolicImage (F : BuildingFacet B') (F' : IncidentFacets B' F) :
    (M.transport T).facetModels.incidentParabolicImage F ((QF.transport T).quotient F) F' =
      M.facetModels.incidentParabolicImage (T.facetEquiv.symm F)
        (QF.quotient (T.facetEquiv.symm F)) (T.incidentEquiv F F') := by
  unfold FacetModelData.incidentParabolicImage
  rw [transport_facetModels_morphism]
  rfl

/-- KP Axiom 4.1.22(5) on `B'`: the parabolic images of incident facets above `F` are those
above `Φ⁻¹ F`, reindexed by `incidentEquiv`. -/
theorem transport_parabolic_order (F : BuildingFacet B') :
    (M.transport T).facetModels.HasFacetParabolicOrderBijection F
      ((QF.transport T).quotient F) := by
  have h₀ := hQF.parabolic_order (T.facetEquiv.symm F)
  have e : (M.transport T).facetModels.incidentParabolicImage F ((QF.transport T).quotient F) =
      M.facetModels.incidentParabolicImage (T.facetEquiv.symm F)
        (QF.quotient (T.facetEquiv.symm F)) ∘ T.incidentEquiv F :=
    funext (transport_incidentParabolicImage T F)
  refine ⟨?_, fun F₁ F₂ h => ?_⟩
  · rw [e]
    exact h₀.1.comp (Set.bijOn_univ.2 (T.incidentEquiv F).bijective)
  · rw [transport_incidentParabolicImage, transport_incidentParabolicImage]
    exact h₀.2 (T.incidentEquiv F F₁) (T.incidentEquiv F F₂) (T.facetPrecedes_symm h)

/-- KP Axiom 4.1.22(6) on `B'`, for the transported root datum. -/
theorem transport_derivative_root_data (F : BuildingFacet B') (g : rationalPoints H)
    (Fa : Set B'.Apartment) (hFa : AffineRootSystem.IsFacet B'.affineRoots Fa)
    (hF : F.val = B'.translatedApartmentMap g '' Fa)
    (hT : IsSplitTorus
      ((M.transport T).torus (BuildingModelIndex.ofFacet F) g Fa hF).torus.toGrp) :
    HasApartmentDerivativeRootDatum B' ((QF.transport T).quotient F)
      ((M.transport T).torus (BuildingModelIndex.ofFacet F) g Fa hF)
      (Droot.transport T.σ f T.comm) hT Fa := by
  have hFa₀ : AffineRootSystem.IsFacet B.affineRoots (T.A.symm '' Fa) := by
    rw [← T.isFacet_apartment_image_iff, T.image_symm_image]
    exact hFa
  exact T.hasApartmentDerivativeRootDatum_transport _ _ (T.conj_comm g) Droot hT Fa
    (hQF.derivative_root_data (T.facetEquiv.symm F) (rationalPoints.map f.inv g) _ hFa₀
      (T.symm_val_eq hF) hT)

/-- KP Axiom 4.1.22(7) on `B'`. -/
theorem transport_positive_radicals (F F' : BuildingFacet B') (_h : FacetPrecedes B' F F') :
    RelativeComponentModelHom.SatisfiesPositiveRadicalClause
      ((QF.transport T).quotient F) ((QF.transport T).quotient F') :=
  (RelativeComponentModelHom.satisfiesPositiveRadicalClause_transport_iff _ _ f).2
    (hQF.positive_radicals _ _ (T.facetPrecedes_symm _h))

/-- All facet clauses of KP Axiom 4.1.22 transfer, for the transported root datum. -/
theorem facetAxiomClauses_transport :
    (QF.transport T).FacetAxiomClauses (Droot.transport T.σ f T.comm) where
  reductive_quotients := transport_reductive_quotients T hQF
  parabolic_images := transport_parabolic_images T hQF
  common_tori F F' h g Fa Fa' hface hF hF' := transport_common_tori T hQF F F' h g Fa Fa' hface hF hF'
  lie_weight_signs F F' h g Fa Fa' hface hF hF' :=
    transport_lie_weight_signs T hQF F F' h g Fa Fa' hface hF hF'
  reduction_preimages := transport_reduction_preimages T hQF
  parabolic_order := transport_parabolic_order T hQF
  derivative_root_data F g Fa hFa hF := transport_derivative_root_data T hQF F g Fa hFa hF
  positive_radicals := transport_positive_radicals T hQF

omit hQF in
/-- Complete KP Axiom 4.1.22 transfers, for the transported root datum. -/
theorem satisfiesMorphismAxioms_transport (hQF : QF.SatisfiesMorphismAxioms Droot) :
    (QF.transport T).SatisfiesMorphismAxioms (Droot.transport T.σ f T.comm) :=
  ⟨BuildingModelFamily.satisfiesGeneralMorphismAxioms_transport T hQF.1,
    facetAxiomClauses_transport T hQF.2⟩

end BuildingModelQuotientFamily
end Langlands.BruhatTits.IntegralModels
