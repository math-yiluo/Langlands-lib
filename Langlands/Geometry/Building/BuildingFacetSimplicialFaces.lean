import Langlands.Geometry.Building.AffineTorsorSimplicialFaces
import Langlands.Geometry.Building.TitsFacetVertexEmbedding
import Langlands.Geometry.Building.RealizationCoordinateAction
import Langlands.Geometry.Building.BaseApartmentRealizationBuilding

/-! # Original quotient simplex faces under actual-vertex independence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

open Set AbstractBuilding

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Entire actual facet vertices, on the type of original quotient vertices. -/
def buildingFacetVertexSet (Fc : BuildingFacet B) :
    Set {x : B.ReducedBuilding // B.IsVertex x} :=
  {x | x.val ∈ B.buildingFacetClosure Fc}

/-- An injective original apartment chart restricts to original vertices. -/
def apartmentVertexEmbedding (hinj : Function.Injective B.apartmentMap)
    (g : rationalPoints G) :
    {a : B.Apartment // AffineRootSystem.IsVertex B.affineRoots a} ↪
      {x : B.ReducedBuilding // B.IsVertex x} where
  toFun a := ⟨B.translatedApartmentMap g a.val, g, a.val, rfl, a.property⟩
  inj' _a _b hab := Subtype.ext
    (B.translatedApartmentMap_injective hinj g (congrArg Subtype.val hab))

/-- The original quotient vertex set is exactly the original chart image. -/
theorem buildingFacetVertexSet_eq_image
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) (g : rationalPoints G) (a : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetVertexSet Fc =
      B.apartmentVertexEmbedding hinj g '' AffineRootSystem.torsorFacetVertexSet B.affineRoots a := by
  ext x
  have hx : x ∈ B.buildingFacetVertexSet Fc ↔ x.val ∈ B.buildingFacetVertices Fc := by
    exact (and_iff_left x.property).symm
  rw [hx, B.buildingFacetVertices_eq_image hD hinj Fc g a hFc]
  constructor
  · rintro ⟨q, ⟨hq, hv⟩, he⟩
    exact ⟨⟨q, hv⟩, hq, Subtype.ext he⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨q.val, ⟨hq, q.property⟩, congrArg Subtype.val he⟩

theorem buildingFacetVertexSet_finite
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : (B.buildingFacetVertexSet Fc).Finite := by
  apply Set.Finite.of_finite_image (s := B.buildingFacetVertexSet Fc) (f := Subtype.val)
    ((B.finite_buildingFacetVertices hD hinj Fc).subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hx, x.property⟩

theorem buildingFacetVertexSet_nonempty
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : (B.buildingFacetVertexSet Fc).Nonempty := by
  obtain ⟨x, hx, hv⟩ := B.buildingFacetVertices_nonempty hD hinj Fc
  exact ⟨⟨x, hv⟩, hx⟩

theorem buildingFacetVertexSet_subset_iff_vertexFinset_subset
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Fd : BuildingFacet B) :
    B.buildingFacetVertexSet Fc ⊆ B.buildingFacetVertexSet Fd ↔
      B.buildingFacetVertexFinset hD hinj Fc ⊆ B.buildingFacetVertexFinset hD hinj Fd := by
  constructor
  · intro h x hx
    obtain ⟨hxc, hxv⟩ := (B.mem_buildingFacetVertexFinset hD hinj Fc x).mp hx
    exact (B.mem_buildingFacetVertexFinset hD hinj Fd x).mpr
      ⟨h (show (⟨x, hxv⟩ : {x // B.IsVertex x}) ∈ B.buildingFacetVertexSet Fc from hxc), hxv⟩
  · intro h x hx
    exact ((B.mem_buildingFacetVertexFinset hD hinj Fd x.val).mp
      (h ((B.mem_buildingFacetVertexFinset hD hinj Fc x.val).mpr ⟨hx, x.property⟩))).1

attribute [local instance] metricRootFintype

local instance buildingFacetSimplicialFacesNormedAddCommGroup : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance buildingFacetSimplicialFacesNormedSpace : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance buildingFacetSimplicialFacesFiniteDimensional : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- Every nonempty subset of a facet's original quotient vertices is the entire
vertex set of another original facet, under actual apartment independence. -/
theorem exists_buildingFacetVertexSet_eq_of_nonempty_subset
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (hind : ∀ a : B.Apartment, AffineIndependent ℝ
      ((↑) : AffineRootSystem.torsorFacetClosureVertexFinset
        hD.isAffineRootSystem_affineRoots a → B.Apartment))
    (Fc : BuildingFacet B) {s : Set {x : B.ReducedBuilding // B.IsVertex x}}
    (hs : s.Nonempty) (hsub : s ⊆ B.buildingFacetVertexSet Fc) :
    ∃ Fd : BuildingFacet B, B.buildingFacetVertexSet Fd = s := by
  obtain ⟨g, _, ⟨a, rfl⟩, hFc⟩ := Fc.property
  let f := B.apartmentVertexEmbedding hinj g
  let t := f ⁻¹' s
  have hsimage : s ⊆ f '' AffineRootSystem.torsorFacetVertexSet B.affineRoots a := by
    simpa only [B.buildingFacetVertexSet_eq_image hD hinj Fc g a hFc] using hsub
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hs
    obtain ⟨q, _, hq⟩ := hsimage hx
    exact ⟨q, by change f q ∈ s; rwa [hq]⟩
  have htsub : t ⊆ AffineRootSystem.torsorFacetVertexSet B.affineRoots a := by
    intro q hq
    obtain ⟨r, hr, he⟩ := hsimage hq
    exact f.injective he ▸ hr
  let e : B.Apartment ≃ᵃ[ℝ] TranslationSpace B.i :=
    (AffineEquiv.vaddConst ℝ (Classical.arbitrary B.Apartment)).symm
  let K := AffineRootSystem.torsorFacetVertexSimplicialComplex
    hD.isAffineRootSystem_affineRoots hind e
  have hface : AffineRootSystem.torsorFacetVertexSet B.affineRoots a ∈ K.faces := by
    rw [AffineRootSystem.faces_torsorFacetVertexSimplicialComplex]
    exact ⟨a, rfl⟩
  have htface := K.mem_of_subset _ hface t htne htsub
  rw [AffineRootSystem.faces_torsorFacetVertexSimplicialComplex] at htface
  obtain ⟨q, hq⟩ := htface
  let Fd : BuildingFacet B :=
    ⟨B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots q,
      ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩
  refine ⟨Fd, ?_⟩
  rw [B.buildingFacetVertexSet_eq_image hD hinj Fd g q rfl, hq]
  exact Set.image_preimage_eq_of_subset (hsimage.trans (Set.image_subset_range _ _))

/-- A simplex complex whose faces are exactly the entire actual vertex sets of
the original quotient facets. -/
def buildingFacetVertexSimplicialComplex
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (hind : ∀ a : B.Apartment, AffineIndependent ℝ
      ((↑) : AffineRootSystem.torsorFacetClosureVertexFinset
        hD.isAffineRootSystem_affineRoots a → B.Apartment)) :
    SimplicialComplex {x : B.ReducedBuilding // B.IsVertex x} where
  faces := Set.range B.buildingFacetVertexSet
  nonempty_vertices := by
    obtain ⟨x, _⟩ := B.buildingFacetVertexSet_nonempty hD hinj
      (B.buildingFacetAt (B.apartmentMap (Classical.arbitrary B.Apartment)))
    exact ⟨x⟩
  finite_of_mem s hs := by
    obtain ⟨Fc, rfl⟩ := hs
    exact B.buildingFacetVertexSet_finite hD hinj Fc
  nonempty_of_mem s hs := by
    obtain ⟨Fc, rfl⟩ := hs
    exact B.buildingFacetVertexSet_nonempty hD hinj Fc
  singleton_mem x :=
    B.exists_buildingFacetVertexSet_eq_of_nonempty_subset hD hinj hind
      (B.buildingFacetAt x.val) (Set.singleton_nonempty x)
      (Set.singleton_subset_iff.mpr
        (B.subset_buildingFacetClosure _ (B.mem_buildingFacetAt x.val)))
  mem_of_subset s hs t ht hts := by
    obtain ⟨Fc, rfl⟩ := hs
    exact B.exists_buildingFacetVertexSet_eq_of_nonempty_subset hD hinj hind Fc ht hts

end ValuationBuildingData

namespace ValuationBuildingData.PolysimplicialRealization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G} (R : B.PolysimplicialRealization)

/-- In each original apartment, the realized complex facets of a
face-compatible realization are ordered exactly as the original closed
apartment facets. -/
def apartmentClosedFacetOrderIso (hR : R.IsFaceCompatible)
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (g : rationalPoints G) :
    Set.range (AffineRootSystem.facetClosure B.affineRoots) ≃o
      R.apartmentComplex (g • B.apartmentImage) := by
  let Fa : B.Apartment → BuildingFacet B := fun p =>
    ⟨B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots p,
      ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩
  let f : Set.range (AffineRootSystem.facetClosure B.affineRoots) →
      R.apartmentComplex (g • B.apartmentImage) := fun C =>
    ⟨(R.realize.symm (Fa C.property.choose)).val,
      (R.realize.symm (Fa C.property.choose)).property, by
        change (R.realize (R.realize.symm (Fa C.property.choose))).val ⊆ _
        rw [Equiv.apply_symm_apply]
        exact B.translatedApartmentMap_image_subset g _⟩
  have hf : ∀ C D, f C ≤ f D ↔ C ≤ D := by
    intro C D
    change (R.realize.symm (Fa C.property.choose)).val ⊆
        (R.realize.symm (Fa D.property.choose)).val ↔ C.val ⊆ D.val
    rw [hR, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      B.facetPrecedes_iff_isFaceOf hD hinj g rfl rfl,
      AffineRootSystem.isFaceOf_facet_iff_facetClosure_subset,
      C.property.choose_spec, D.property.choose_spec]
  refine OrderIso.ofSurjective (OrderEmbedding.ofMapLEIff f hf) ?_
  rintro ⟨S, hS, hSY⟩
  obtain ⟨p, hp⟩ := B.exists_facet_presentation_in_apartment hD (R.realize ⟨S, hS⟩) g hSY
  refine ⟨⟨AffineRootSystem.facetClosure B.affineRoots p, p, rfl⟩, ?_⟩
  have hFa : Fa (⟨AffineRootSystem.facetClosure B.affineRoots p, p, rfl⟩ :
      Set.range (AffineRootSystem.facetClosure B.affineRoots)).property.choose =
        R.realize ⟨S, hS⟩ := by
    apply Subtype.ext
    refine Eq.trans ?_ hp.symm
    change B.translatedApartmentMap g '' _ = B.translatedApartmentMap g '' _
    rw [AffineRootSystem.facet_eq_facet_iff.mpr
      (AffineRootSystem.facetClosure_eq_facetClosure_iff.mp
        (⟨AffineRootSystem.facetClosure B.affineRoots p, p, rfl⟩ :
          Set.range (AffineRootSystem.facetClosure B.affineRoots)).property.choose_spec)]
  apply Subtype.ext
  change (R.realize.symm (Fa _)).val = S
  rw [hFa, Equiv.symm_apply_apply]

attribute [local instance] metricRootFintype

local instance buildingFacetSimplicialFacesNormedAddCommGroup2 : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance buildingFacetSimplicialFacesNormedSpace2 : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance buildingFacetSimplicialFacesFiniteDimensional2 : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- Under actual-vertex independence in the original apartment, every original
apartment complex of a face-compatible realization is polysimplicial. -/
theorem isPolysimplicial_apartmentComplex_of_affineIndependent
    (hR : R.IsFaceCompatible)
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (hind : ∀ a : B.Apartment, AffineIndependent ℝ
      ((↑) : AffineRootSystem.torsorFacetClosureVertexFinset
        hD.isAffineRootSystem_affineRoots a → B.Apartment))
    {Y : Set B.ReducedBuilding} (hY : B.IsApartment Y) :
    AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y) := by
  obtain ⟨g, rfl⟩ := hY
  exact (AffineRootSystem.isPolysimplicial_torsorClosedFacets_of_affineIndependent
    hD.isAffineRootSystem_affineRoots hind).of_orderIso
      (R.apartmentClosedFacetOrderIso hR hD hinj g)

end ValuationBuildingData.PolysimplicialRealization

namespace ParahoricBuildingData.IsBuildingTitsSystem

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}
  (hT : P.IsBuildingTitsSystem Ca π Sgen)
  (hD : P.toValuationBuildingData.SatisfiesApartmentAxioms)
  (hinj : Function.Injective P.apartmentMap)

local notation "B" => P.toValuationBuildingData

attribute [local instance] ValuationBuildingData.metricRootFintype

local instance buildingFacetSimplicialFacesNormedAddCommGroup3 : NormedAddCommGroup (TranslationSpace P.i) :=
  RootTranslationMetric.normedAddCommGroup P.i

local instance buildingFacetSimplicialFacesNormedSpace3 : NormedSpace ℝ (TranslationSpace P.i) :=
  RootTranslationMetric.normedSpace P.i

local instance buildingFacetSimplicialFacesFiniteDimensional3 : FiniteDimensional ℝ (TranslationSpace P.i) :=
  RootTranslationMetric.finiteDimensional P.i

variable (hind : ∀ a : P.Apartment, AffineIndependent ℝ
  ((↑) : AffineRootSystem.torsorFacetClosureVertexFinset
    hD.isAffineRootSystem_affineRoots a → P.Apartment))

include hT hD hinj

/-- Full actual Tits comparison identifies original incidence with inclusion
of original vertex sets. -/
theorem facetPrecedes_iff_vertexSet_subset (Fc Fd : BuildingFacet B) :
    FacetPrecedes B Fc Fd ↔ P.toValuationBuildingData.buildingFacetVertexSet Fc ⊆ P.toValuationBuildingData.buildingFacetVertexSet Fd :=
  (hT.facetPrecedes_iff_vertexFinset_subset hD hinj Fc Fd).trans
    (P.toValuationBuildingData.buildingFacetVertexSet_subset_iff_vertexFinset_subset hD hinj Fc Fd).symm

/-- Original facets, with their original incidence order, are exactly the
simplices on the original quotient vertices. -/
def buildingFacetSimplicialOrderIso :
    @OrderIso (BuildingFacet B)
      (P.toValuationBuildingData.buildingFacetVertexSimplicialComplex hD hinj hind).faces
      (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj).toLE inferInstance :=
  @OrderIso.ofSurjective _ _
    (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj).toLE inferInstance
    (@OrderEmbedding.ofMapLEIff _ _
      (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj) inferInstance
      (fun Fc => (⟨P.toValuationBuildingData.buildingFacetVertexSet Fc, Fc, rfl⟩ :
        (P.toValuationBuildingData.buildingFacetVertexSimplicialComplex hD hinj hind).faces))
      (fun Fc Fd => (hT.facetPrecedes_iff_vertexSet_subset hD hinj Fc Fd).symm))
    (by
      rintro ⟨s, Fc, rfl⟩
      exact ⟨Fc, rfl⟩)

/-- One factor, with vertices the original vertices of the original quotient. -/
def buildingFacetVertexPolysimplicialComplex :
    PolysimplicialComplex PUnit (fun _ => {x : P.ReducedBuilding // P.toValuationBuildingData.IsVertex x}) :=
  ⟨fun _ => P.toValuationBuildingData.buildingFacetVertexSimplicialComplex hD hinj hind⟩

/-- Original incidence is the order on the one-factor polysimplicial facets. -/
def buildingFacetPolysimplicialOrderIso :
    @OrderIso (BuildingFacet B)
      (buildingFacetVertexPolysimplicialComplex hD hinj hind).facets
      (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj).toLE inferInstance :=
  letI : LE (BuildingFacet B) := (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj).toLE
  ((hT.buildingFacetSimplicialOrderIso hD hinj hind).trans
    (OrderIso.funUnique PUnit (P.toValuationBuildingData.buildingFacetVertexSimplicialComplex hD hinj hind).faces).symm).trans
      (buildingFacetVertexPolysimplicialComplex hD hinj hind).facetsOrderIso.symm

/-- A literal realization by the original facets of the original valuation
quotient; no replacement carrier or subdivision is used. -/
def buildingFacetSimplicialRealization : P.toValuationBuildingData.PolysimplicialRealization where
  index := PUnit
  V _ := {x : P.ReducedBuilding // P.toValuationBuildingData.IsVertex x}
  complex := buildingFacetVertexPolysimplicialComplex hD hinj hind
  realize := (hT.buildingFacetPolysimplicialOrderIso hD hinj hind).toEquiv.symm

theorem buildingFacetSimplicialRealization_isFaceCompatible :
    (hT.buildingFacetSimplicialRealization hD hinj hind).IsFaceCompatible := by
  let _ : LE (BuildingFacet B) := (P.toValuationBuildingData.buildingFacetPartialOrder hD hinj).toLE
  intro Fc Fd
  change Fc ≤ Fd ↔
    (hT.buildingFacetPolysimplicialOrderIso hD hinj hind).symm Fc ≤
      (hT.buildingFacetPolysimplicialOrderIso hD hinj hind).symm Fd
  exact (hT.buildingFacetPolysimplicialOrderIso hD hinj hind).symm.map_rel_iff.symm

/-- The original rational-point action induces a polysimplicial action on this
one-factor realization. -/
theorem buildingFacetSimplicialRealization_isPolysimplicialAction :
    (hT.buildingFacetSimplicialRealization hD hinj hind).IsPolysimplicialAction := by
  let R := hT.buildingFacetSimplicialRealization hD hinj hind
  apply (R.isPolysimplicialAction_iff_respectsCoordinateFibers
    (hT.buildingFacetSimplicialRealization_isFaceCompatible hD hinj hind)).mpr
  intro g
  refine ⟨Equiv.refl _, ?_⟩
  intro i x y hxy
  have heq : x = y := funext fun j => by
    obtain rfl : j = i := Subsingleton.elim (α := PUnit.{u + 1}) j i
    exact hxy
  rw [heq]

/-- With actual simple-reflection admissibility, the one-factor realization
and its original apartments form a building. -/
theorem buildingFacetSimplicialRealization_isBuilding
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s}) :
    AbstractBuilding.IsBuilding (hT.buildingFacetSimplicialRealization hD hinj hind).complex
      (hT.buildingFacetSimplicialRealization hD hinj hind).apartments :=
  hT.realization_isBuilding _ (hT.buildingFacetSimplicialRealization_isFaceCompatible hD hinj hind)
    hadm fun _ hY =>
      ValuationBuildingData.PolysimplicialRealization.isPolysimplicial_apartmentComplex_of_affineIndependent
        _ (hT.buildingFacetSimplicialRealization_isFaceCompatible hD hinj hind) hD hinj hind hY

end ParahoricBuildingData.IsBuildingTitsSystem

end Langlands.Geometry.Building
