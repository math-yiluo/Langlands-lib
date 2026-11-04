import Langlands.BruhatTits.IntegralModels.IntegralTorus
import Langlands.BruhatTits.IntegralModels.FacetParabolicOrder
import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Mathlib.Topology.Order.OrderClosed

/-! # The actual bounded-subset family of KP integral models

The domain consists of actual nonempty bounded apartment subsets and actual
building facets. A subset has one index even when several charts present it.
The assertions below concern supplied models, not their existence.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The real affine topology, specified without choosing a norm or an origin:
the initial topology of all real affine functionals. -/
@[instance_reducible] def affineApartmentTopology : TopologicalSpace B.Apartment :=
  ⨅ f : B.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance

/-- Ordinary topological closure in the real affine apartment. This is distinct
from the union of closures of facets meeting a set (KP Definition 4.1.14). -/
def apartmentClosure (Ω : Set B.Apartment) : Set B.Apartment :=
  @closure _ (affineApartmentTopology B) Ω

/-- Every real affine functional is continuous for the specified apartment topology. -/
theorem continuous_affineApartmentFunctional (f : B.Apartment →ᵃ[ℝ] ℝ) :
    @Continuous _ _ (affineApartmentTopology B) inferInstance f :=
  continuous_iff_le_induced.mpr (iInf_le _ f)

/-- Closing a bounded subset keeps every affine functional bounded above. -/
theorem isBoundedSubset_apartmentClosure {Ω : Set B.Apartment}
    (hΩ : B.IsBoundedSubset Ω) : B.IsBoundedSubset (apartmentClosure B Ω) := by
  let := affineApartmentTopology B
  intro f
  exact (hΩ f).closure.mono
    (image_closure_subset_closure_image (continuous_affineApartmentFunctional B f))

/-- Nonemptiness is preserved by ordinary apartment closure. -/
theorem nonempty_apartmentClosure {Ω : Set B.Apartment} (hΩ : Ω.Nonempty) :
    (apartmentClosure B Ω).Nonempty := by
  let := affineApartmentTopology B
  exact hΩ.mono subset_closure

/-- Actual building subsets with a nonempty bounded presentation in one of the
existing translated apartment charts. -/
def IsNonemptyBoundedApartmentSubset (Ω : Set B.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (Ωa : Set B.Apartment),
    Ωa.Nonempty ∧ B.IsBoundedSubset Ωa ∧
      Ω = B.translatedApartmentMap g '' Ωa

/-- A common domain for the bounded-subset clauses and the whole-building facet
clauses. Facets are admitted explicitly before proving their boundedness from
the surrounding affine-root-system axioms. -/
abbrev BuildingModelIndex : Type u :=
  {Ω : Set B.ReducedBuilding //
    IsNonemptyBoundedApartmentSubset B Ω ∨ B.IsFacet Ω}

namespace BuildingModelIndex

variable {B}

/-- The index belonging to an actual nonempty bounded subset in any translated chart. -/
def ofApartment (g : rationalPoints G) (Ωa : Set B.Apartment)
    (hne : Ωa.Nonempty) (hb : B.IsBoundedSubset Ωa) : BuildingModelIndex B :=
  ⟨B.translatedApartmentMap g '' Ωa, Or.inl ⟨g, Ωa, hne, hb, rfl⟩⟩

/-- The index of an actual whole-building facet. -/
def ofFacet (F : BuildingFacet B) : BuildingModelIndex B :=
  ⟨F.val, Or.inr F.property⟩

/-- Equal actual subsets give equal indices, independently of apartment presentations. -/
theorem ext {Ω Ω' : BuildingModelIndex B} (h : Ω.val = Ω'.val) : Ω = Ω' :=
  Subtype.ext h

/-- Every index denotes a nonempty actual subset of the building. -/
theorem nonempty (Ω : BuildingModelIndex B) : Ω.val.Nonempty := by
  rcases Ω.property with ⟨g, Ωa, hne, _, h⟩ | ⟨g, Fa, ⟨x, hx⟩, h⟩
  · rw [h]
    exact hne.image _
  · rw [h, ← hx]
    exact ⟨_, x, AffineRootSystem.mem_facet_self _ _, rfl⟩

end BuildingModelIndex

/-- The general ordered-subset hypothesis: both subsets have presentations in
one translated apartment with `Ωa ⊆ closure Ωa'` (KP Notation 1.3.34). -/
def ApartmentSubsetPrecedes (Ω Ω' : BuildingModelIndex B) : Prop :=
  ∃ (g : rationalPoints G) (Ωa Ωa' : Set B.Apartment),
    Ω.val = B.translatedApartmentMap g '' Ωa ∧
      Ω'.val = B.translatedApartmentMap g '' Ωa' ∧
        Ωa ⊆ apartmentClosure B Ωa'

/-- Exactly the two kinds of arrows required in KP 4.1.22: ordinary
closure-ordered subsets in a common apartment, and incident actual facets.
The second presentation lets the existing chart-defined facet interface be used
before the surrounding building axioms identify its closure formula topologically. -/
def ModelMorphismRequired (Ω Ω' : BuildingModelIndex B) : Prop :=
  ApartmentSubsetPrecedes B Ω Ω' ∨
    ∃ (F F' : BuildingFacet B),
      Ω.val = F.val ∧ Ω'.val = F'.val ∧ FacetPrecedes B F F'

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

/-- Supplied actual models on the common subset domain, their identity-generic
comparison maps, and the integral split torus for every apartment presentation.
The torus over the chart `g A(S)` has generic inclusion `Int(g) ∘ i`. -/
structure BuildingModelFamily where
  model : BuildingModelIndex B → RelativeComponentModelData R K G
  morphism : ∀ (Ω Ω' : BuildingModelIndex B), ModelMorphismRequired B Ω Ω' →
    RelativeComponentModelHom (model Ω') (model Ω)
  torus : ∀ (Ω : BuildingModelIndex B) (g : rationalPoints G)
    (Ωa : Set B.Apartment), Ω.val = B.translatedApartmentMap g '' Ωa →
      IntegralTorusData (model Ω) B.S (B.i ≫ (G.innerIso g).hom)

namespace BuildingModelFamily

variable {B R} (M : BuildingModelFamily B R)

/-- The whole-building facet models are restrictions of the same actual family.
No independently chosen model, quotient, or comparison is introduced. -/
def facetModels : FacetModelData B R where
  model F := M.model (BuildingModelIndex.ofFacet F)
  morphism F F' h :=
    M.morphism _ _ (Or.inr ⟨F, F', rfl, rfl, h⟩)

/-- The generic-identity comparison for each ordinary closure-ordered pair. -/
def apartmentMorphism (Ω Ω' : BuildingModelIndex B)
    (h : ApartmentSubsetPrecedes B Ω Ω') :
    RelativeComponentModelHom (M.model Ω') (M.model Ω) :=
  M.morphism Ω Ω' (Or.inl h)

variable (P : ParahoricBuildingData G)

/-- The actual `G(K)^1_Ω`, using the pointwise fixer of the actual building subset. -/
def oneFixer (Ω : BuildingModelIndex B) : Subgroup (rationalPoints G) :=
  B.apartment.pointwiseFixer Ω.val ⊓ Langlands.Plancherel.rationalCommonNormKernel G

/-- The actual `G(K)^0_Ω`, using the same zero subgroup and actual building action.
The equality of building data below permits the same `P` in all other clauses. -/
def zeroFixer (Ω : BuildingModelIndex B) : Subgroup (rationalPoints G) :=
  B.apartment.pointwiseFixer Ω.val ⊓ P.zeroSubgroup

section Residue

variable [IsLocalRing R]

/-- A generic-identity isomorphism of actual neutral models, rather than an
equality of their chosen presentations. -/
def NeutralModelsIsomorphic (Ω Ω' : BuildingModelIndex B) : Prop :=
  ∃ φ : (M.model Ω).neutral.Hom (M.model Ω').neutral (𝟙 G), IsIso φ.hom

/-- Complete KP Axiom 4.1.20 on this actual subset-indexed model family.
The relative-component, smoothness, affineness and connected-fibre assertions
are already part of each `RelativeComponentModelData`. -/
structure ModelAxiomClauses : Prop where
  /-- The supplied parahoric datum is the same building datum. -/
  building_eq : P.toValuationBuildingData = B
  /-- Full integral sections realize exactly the one-group fixer. -/
  full_points : ∀ Ω, (M.model Ω).full.integralPoints = oneFixer Ω
  /-- Neutral integral sections realize exactly the zero-group fixer. -/
  neutral_points : ∀ Ω, (M.model Ω).neutral.integralPoints = zeroFixer P Ω
  /-- Part (1): a nonempty subset of a facet has the same neutral model. -/
  facet_constancy : ∀ (Ω : BuildingModelIndex B) (F : BuildingFacet B),
    Ω.val ⊆ F.val → M.NeutralModelsIsomorphic Ω (BuildingModelIndex.ofFacet F)
  /-- Part (2): ordinary topological closure does not change the neutral model. -/
  closure_invariance : ∀ (g : rationalPoints G) (Ωa : Set B.Apartment)
    (hne : Ωa.Nonempty) (hb : B.IsBoundedSubset Ωa),
      M.NeutralModelsIsomorphic
        (BuildingModelIndex.ofApartment g Ωa hne hb)
        (BuildingModelIndex.ofApartment g (apartmentClosure B Ωa)
          (nonempty_apartmentClosure B hne) (isBoundedSubset_apartmentClosure B hb))
  /-- Part (3), for every actual apartment presentation of the subset. -/
  torus_clause : ∀ (Ω : BuildingModelIndex B) (g : rationalPoints G)
    (Ωa : Set B.Apartment) (h : Ω.val = B.translatedApartmentMap g '' Ωa),
      (M.torus Ω g Ωa h).SatisfiesTorusClause
  /-- Part (4): equality of full and neutral models in the simply connected case. -/
  simply_connected : ∀ Ω, (M.model Ω).HasEqualComponentsForSimplyConnected

/-- The complete supplied-family validity predicate for KP Axiom 4.1.20.
The fields of `ModelAxiomClauses` expose each assertion. -/
def SatisfiesModelAxioms : Prop :=
  M.ModelAxiomClauses P

/-- The complete preamble and part (1) of KP Axiom 4.1.22, including all
ordered nonempty bounded subsets. Identity-generic compatibility, restriction
to components and the integral-point inclusions are encoded by the supplied maps. -/
def SatisfiesGeneralMorphismAxioms : Prop :=
  ∀ (Ω Ω' : BuildingModelIndex B) (h : ModelMorphismRequired B Ω Ω'),
    (M.morphism Ω Ω' h).SatisfiesGeneralSpecialFibreClauses

end Residue
end BuildingModelFamily
end Langlands.BruhatTits.IntegralModels
