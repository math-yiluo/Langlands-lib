import Langlands.BruhatTits.IntegralModels.ModelFamily
import Langlands.BruhatTits.IntegralModels.FacetRootDatum

/-! # The complete KP model-morphism and facet clauses

All quotients belong to the same subset-indexed model family. The formulas in a
translated apartment use its original abstract split torus with the conjugated
generic inclusion. This unit asserts no validity or existence theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance facetAxioms_neutralSpecialFibre_affine
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance facetAxioms_neutralSpecialFibre_isAffine
    (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

local instance facetAxioms_quotient_isAffine {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) : IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)
  {j : B.S.toGrp ⟶ G} (T : IntegralTorusData source B.S j)

/-- The Lie-weight formula in the coordinates of any translated apartment.
Its torus inclusion may be conjugated; the abstract torus and its lattices are
those used for the apartment coordinates. -/
def HasApartmentLieWeightSignFormula (hT : IsSplitTorus T.torus.toGrp)
    (Fa Fa' : Set B.Apartment) : Prop :=
  ∀ x ∈ Fa, ∀ v : RealTorusSpace.V B.S,
    (Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ x ∈ Fa' →
      nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
        {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
          0 ≤ RealTorusSpace.eval B.S ((T.characterSpecialization hT).symm χ) v}

/-- On the original apartment this is the previously defined raw sign clause. -/
theorem apartmentLieWeightSignFormula_eq
    (T₀ : IntegralTorusData source B.S B.i)
    (hT : IsSplitTorus T₀.torus.toGrp) (Fa Fa' : Set B.Apartment) :
    φ.HasApartmentLieWeightSignFormula B Q T₀ hT Fa Fa' ↔
      φ.HasLieWeightSignFormula B Q T₀ hT Fa Fa' :=
  Iff.rfl

end RelativeComponentModelHom

variable {D : RelativeComponentModelData R K G}
  (Q : SpecialFibreQuotientData D)
  {j : B.S.toGrp ⟶ G} (T : IntegralTorusData D B.S j)
  (Droot : RelativeRootReflectionData B.i)

/-- The derivative root-coroot graph in a translated apartment. The original
torus `S` parametrizes the conjugated torus, so both lattice transports still
come from the same actual integral torus. -/
def apartmentDerivativeRootCorootGraph (hT : IsSplitTorus T.torus.toGrp)
    (Fa : Set B.Apartment) :
    Set (characterLattice T.specialFibre × cocharacterLattice T.specialFibre) :=
  {p | ∃ a : relativeRoots B.i, a.val ∈ facetDerivativeRoots B Fa ∧
    p = (T.characterSpecialization hT a.val,
      T.cocharacterSpecialization hT (Droot.coroot a))}

/-- The root datum is on the actual maximal reductive quotient of this facet's
model, with the direct image of this facet's own integral torus. -/
def HasApartmentDerivativeRootDatum (hT : IsSplitTorus T.torus.toGrp)
    (Fa : Set B.Apartment) : Prop :=
  ∃ (J : Type u) (_ : Finite J)
    (P : RootDatum J (characterLattice T.specialFibre) (cocharacterLattice T.specialFibre)),
      IsRootDatumOf (T.specialFibreInclusion ≫ Q.projection) P ∧
        Set.range (fun k => (P.root k, P.coroot k)) =
          apartmentDerivativeRootCorootGraph B T Droot hT Fa

/-- On the original torus the graph is the previously defined raw graph. -/
theorem apartmentDerivativeRootCorootGraph_eq
    (T₀ : IntegralTorusData D B.S B.i) (hT : IsSplitTorus T₀.torus.toGrp)
    (Fa : Set B.Apartment) :
    apartmentDerivativeRootCorootGraph B T₀ Droot hT Fa =
      facetDerivativeRootCorootGraph B T₀ Droot hT Fa :=
  rfl

variable (M : BuildingModelFamily B R)

/-- Supplied radicals and quotients for exactly the facet restriction of the
given common model family, rather than independently chosen facet models. -/
structure BuildingModelQuotientFamily where
  quotient : ∀ F : BuildingFacet B, SpecialFibreQuotientData (M.facetModels.model F)

namespace BuildingModelQuotientFamily

variable {B M} (QF : BuildingModelQuotientFamily B M)

/-- All facet-specific clauses of KP Axiom 4.1.22. Every chart and model map
here belongs to the same actual building and the same subset-indexed family. -/
structure FacetAxiomClauses (Droot : RelativeRootReflectionData B.i) : Prop where
  /-- The quotient in the source is the actual maximal reductive quotient. -/
  reductive_quotients : ∀ F, (QF.quotient F).IsReductiveQuotient
  /-- Part (2): the neutral special-fibre image is parabolic. -/
  parabolic_images : ∀ F F' (h : FacetPrecedes B F F'),
    (M.facetModels.morphism F F' h).HasParabolicSpecialFibreImage
  /-- Part (3), first paragraph, in every common translated chart. Splitting
  of the integral torus is retained explicitly for the lattice formulas. -/
  common_tori : ∀ F F' (h : FacetPrecedes B F F')
    (g : rationalPoints G) (Fa Fa' : Set B.Apartment),
    AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' →
    F.val = B.translatedApartmentMap g '' Fa →
    ∀ hF' : F'.val = B.translatedApartmentMap g '' Fa',
      let T := M.torus (BuildingModelIndex.ofFacet F') g Fa' hF'
      T.IsClosedSplit ∧
        (M.facetModels.morphism F F' h).HasMaximalSplitTori (QF.quotient F) T
  /-- Part (3), second paragraph: equality of all nonzero Lie weights with
  the quotient roots satisfying the source's nonnegative sign condition. -/
  lie_weight_signs : ∀ F F' (h : FacetPrecedes B F F')
    (g : rationalPoints G) (Fa Fa' : Set B.Apartment),
    AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' →
    F.val = B.translatedApartmentMap g '' Fa →
    ∀ hF' : F'.val = B.translatedApartmentMap g '' Fa',
      let T := M.torus (BuildingModelIndex.ofFacet F') g Fa' hF'
      ∀ hT : IsSplitTorus T.torus.toGrp,
        (M.facetModels.morphism F F' h).HasApartmentLieWeightSignFormula
          B (QF.quotient F) T hT Fa Fa'
  /-- Part (4): the full residue-field-point subgroup of the schematic image
  has precisely the stated reduction preimage in integral sections. -/
  reduction_preimages : ∀ F F' (h : FacetPrecedes B F F'),
    (M.facetModels.morphism F F' h).HasParabolicReductionPreimage
  /-- Part (5): all incident actual building facets, all parabolics, and
  the literal opposite-inclusion order direction. -/
  parabolic_order : ∀ F,
    M.facetModels.HasFacetParabolicOrderBijection F (QF.quotient F)
  /-- Part (6): the complete paired root-coroot graph for every facet
  presentation, on the direct image of its own integral torus. -/
  derivative_root_data : ∀ (F : BuildingFacet B)
    (g : rationalPoints G) (Fa : Set B.Apartment),
    AffineRootSystem.IsFacet B.affineRoots Fa →
    ∀ hF : F.val = B.translatedApartmentMap g '' Fa,
      let T := M.torus (BuildingModelIndex.ofFacet F) g Fa hF
      ∀ hT : IsSplitTorus T.torus.toGrp,
        HasApartmentDerivativeRootDatum B (QF.quotient F) T Droot hT Fa
  /-- Part (7), including the reduction surjectivity stated in the source. -/
  positive_radicals : ∀ F F' (_h : FacetPrecedes B F F'),
    RelativeComponentModelHom.SatisfiesPositiveRadicalClause
      (QF.quotient F) (QF.quotient F')

/-- The facet-specific predicate; its clauses are exposed as named fields. -/
def SatisfiesFacetAxioms (Droot : RelativeRootReflectionData B.i) : Prop :=
  QF.FacetAxiomClauses Droot

/-- Complete KP Axiom 4.1.22, on the same model family used in 4.1.20:
general bounded-subset morphisms and all seven facet properties. -/
def SatisfiesMorphismAxioms (Droot : RelativeRootReflectionData B.i) : Prop :=
  M.SatisfiesGeneralMorphismAxioms ∧ QF.SatisfiesFacetAxioms Droot

/-- The complete predicate exposes the general bounded-subset clauses. -/
theorem SatisfiesMorphismAxioms.general
    {Droot : RelativeRootReflectionData B.i} (h : QF.SatisfiesMorphismAxioms Droot) :
    M.SatisfiesGeneralMorphismAxioms :=
  h.1

/-- The complete predicate exposes all facet clauses on the same data. -/
theorem SatisfiesMorphismAxioms.facets
    {Droot : RelativeRootReflectionData B.i} (h : QF.SatisfiesMorphismAxioms Droot) :
    QF.FacetAxiomClauses Droot :=
  h.2

end BuildingModelQuotientFamily
end Langlands.BruhatTits.IntegralModels
