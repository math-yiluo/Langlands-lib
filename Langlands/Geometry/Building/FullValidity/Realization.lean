import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.AbstractBuilding
import Langlands.BruhatTits.IntegralModels.FacetParabolicOrder
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.ConjugacyStatement

/-!
# The building of Axiom 4.1.1 on the reduced building of valuation data

For building data `B : ValuationBuildingData G` over a nonarchimedean local field `F`, this
module states the clauses of KP Axiom 4.1.1 that concern one group `G`, on the reduced
building `B(G)` of `B` (KP (7.6.2), Remark 7.6.5):

* `B.PolysimplicialRealization`: supplied data of a polysimplicial complex `K`
  (KP Definition 1.5.1) together with a bijection between the facets of `K` and the facets of
  `B(G)`. This is how KP's polysimplicial complex `B(G)` and its geometric realization are
  linked ("From now on we will not distinguish between the polysimplicial complex `B(G)` and its
  geometric realization", KP after Remark 4.1.5). Facets of `B(G)` are
  `IntegralModels.BuildingFacet B` and the face relation (KP Notation 1.3.34 and the paragraph
  after Axiom 4.1.1) is `IntegralModels.FacetPrecedes B`, read in a common apartment `g · A(S)`;
  both are the ones used by the integral-model clauses of Axioms 4.1.20 and 4.1.22.
* `R.apartments`: the apartments of `K`, the sets of facets of `K` realized inside an apartment
  `g · A(S)` of `B(G)`.
* `R.IsPolysimplicialAction`: every `g ∈ G(F)` acts on `K` by a polysimplicial automorphism
  inducing the action of `g` on the facets of `B(G)`.
* `maximalSplitTori G`, `B.conjTorus g = g S g⁻¹`, and `B.HasTorusApartmentCorrespondence`: the
  bijective `G(F)`-equivariant correspondence `g S g⁻¹ ↦ g · A(S)` between maximal split tori
  and apartments.
* `B.SatisfiesBuildingAxiom R`: the clauses of KP Axiom 4.1.1 for `G`, namely face compatibility
  of the realization, KP Definition 1.5.5 (`AbstractBuilding.IsBuilding`), the polysimplicial
  action, the torus–apartment correspondence and the stabilizer clause
  `B.HasNormalizerApartmentStabilizer`.

The comparisons of Axiom 4.1.1 for surjective homomorphisms with central kernel relate the
buildings of different groups, so they are not stated here. They belong on families of data for
all groups. Nothing here asserts that any of these predicates holds, or that data exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The maximal split tori of `G`, as subgroup functors of `G`: the images of the maximal split
tori `i' : S' → G` (`IsMaximalSplitTorus`). A maximal split torus is a closed immersion, so it is
determined by its image up to unique isomorphism over `G`. -/
def maximalSplitTori (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] :
    Set (SubgroupFunctor G) :=
  {T | ∃ (S' : CommGroupScheme (Spec (CommRingCat.of F))) (i' : S'.toGrp ⟶ G),
    IsMaximalSplitTorus i' ∧ SubgroupFunctor.range i' = T}

namespace ValuationBuildingData

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-! ### Maximal split tori and apartments -/

/-- The maximal split torus `g S g⁻¹` of `G`, the image of `i` followed by the inner
automorphism `Int(g)` of `G`. -/
def conjTorus (g : rationalPoints G) : SubgroupFunctor G :=
  SubgroupFunctor.range (B.i ≫ (G.innerIso g).hom)

theorem conjTorus_mem_maximalSplitTori (g : rationalPoints G) :
    B.conjTorus g ∈ maximalSplitTori G :=
  ⟨B.S, B.i ≫ (G.innerIso g).hom, B.isMaximalSplitTorus.comp_iso _, rfl⟩

/-- A chart of an actual torus `i₂ : T₂ → G` at `h ∈ G(F)`: an isomorphism `σ : S ≅ T₂` with
`i ≫ Int(h) = σ ≫ i₂`, so that `T₂ = h S h⁻¹` with its embedding. -/
def IsTorusChart {T₂ : CommGroupScheme (Spec (CommRingCat.of F))} (i₂ : T₂.toGrp ⟶ G)
    (h : rationalPoints G) (σ : B.S ≅ T₂) : Prop :=
  B.i ≫ (G.innerIso h).hom = CommGroupScheme.groupHom σ.hom ≫ i₂

variable {B} in
/-- A torus with a chart at `h` is `h S h⁻¹`. -/
theorem IsTorusChart.conjTorus_eq {T₂ : CommGroupScheme (Spec (CommRingCat.of F))}
    {i₂ : T₂.toGrp ⟶ G} {h : rationalPoints G} {σ : B.S ≅ T₂} (hc : B.IsTorusChart i₂ h σ) :
    B.conjTorus h = SubgroupFunctor.range i₂ := by
  rw [conjTorus, hc]
  let e : B.S.toGrp ≅ T₂.toGrp :=
    { hom := CommGroupScheme.groupHom σ.hom
      inv := CommGroupScheme.groupHom σ.inv
      hom_inv_id := congrArg Additive.toMul σ.hom_inv_id
      inv_hom_id := congrArg Additive.toMul σ.inv_hom_id }
  exact SubgroupFunctor.range_iso_comp e i₂

/-- The clause of KP Axiom 4.1.1 that the apartments of `B(G)` are in bijective
`G(F)`-equivariant correspondence with the maximal split tori of `G`, with `A(S)` corresponding
to `S`. Equivariance forces the apartment of `g S g⁻¹` to be `g · A(S)`. The clause says that

* every actual maximal split torus `i₂ : T₂ → G` has a chart: it is `h S h⁻¹` for some
  `h ∈ G(F)`, through an isomorphism `σ : S ≅ T₂` (so the correspondence is defined on all
  maximal split tori; `exists_conjTorus_eq` is the form for subgroup functors), and
* `g S g⁻¹ = h S h⁻¹` exactly when `g · A(S) = h · A(S)` (so `g S g⁻¹ ↦ g · A(S)` is well
  defined and injective).

The correspondence is then surjective onto the apartments `g · A(S)` (`IsApartment`) and
`G(F)`-equivariant by construction. The first clause is the `G(F)`-conjugacy of maximal split
tori; it follows from `MaximalSplitTorusConjugacyStatement`
(`exists_torusChart_of_maximalSplitTorusConjugacy`), which is not proved in the Library, so it
is kept as a clause. -/
structure HasTorusApartmentCorrespondence : Prop where
  /-- Every actual maximal split torus of `G` is `G(F)`-conjugate to `S`. -/
  exists_torusChart : ∀ (T₂ : CommGroupScheme (Spec (CommRingCat.of F))) (i₂ : T₂.toGrp ⟶ G),
    IsMaximalSplitTorus i₂ → ∃ (h : rationalPoints G) (σ : B.S ≅ T₂), B.IsTorusChart i₂ h σ
  /-- `g S g⁻¹ = h S h⁻¹` if and only if `g · A(S) = h · A(S)`. -/
  conjTorus_eq_iff : ∀ g h : rationalPoints G,
    B.conjTorus g = B.conjTorus h ↔ g • B.apartmentImage = h • B.apartmentImage

/-- The conjugacy of maximal split tori (`MaximalSplitTorusConjugacyStatement`) gives the first
clause of `HasTorusApartmentCorrespondence`. -/
theorem exists_torusChart_of_maximalSplitTorusConjugacy
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (T₂ : CommGroupScheme (Spec (CommRingCat.of F))) (i₂ : T₂.toGrp ⟶ G)
    (hi₂ : IsMaximalSplitTorus i₂) :
    ∃ (h : rationalPoints G) (σ : B.S ≅ T₂), B.IsTorusChart i₂ h σ := by
  obtain ⟨h, e, he⟩ :=
    (hconj F G B.isConnectedReductive).1 B.S T₂ B.i i₂ B.isMaximalSplitTorus hi₂
  let σ : B.S ≅ T₂ :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact ⟨h, σ, he⟩

/-- Every maximal split torus of `G`, as a subgroup functor, is `g S g⁻¹` for some `g ∈ G(F)`. -/
theorem HasTorusApartmentCorrespondence.exists_conjTorus_eq {B : ValuationBuildingData G}
    (h : B.HasTorusApartmentCorrespondence) :
    ∀ T ∈ maximalSplitTori G, ∃ g : rationalPoints G, B.conjTorus g = T := by
  rintro T ⟨T₂, i₂, hi₂, rfl⟩
  obtain ⟨g, σ, hc⟩ := h.exists_torusChart T₂ i₂ hi₂
  exact ⟨g, hc.conjTorus_eq⟩

/-- The apartment corresponding to a subgroup functor `T` of `G`: the union of the apartments
`g · A(S)` with `g S g⁻¹ = T`. Under `HasTorusApartmentCorrespondence` it is the apartment of the
maximal split torus `T`. -/
def torusApartment (T : SubgroupFunctor G) : Set B.ReducedBuilding :=
  {y | ∃ g : rationalPoints G, B.conjTorus g = T ∧ y ∈ g • B.apartmentImage}

theorem HasTorusApartmentCorrespondence.torusApartment_conjTorus
    {B : ValuationBuildingData G} (h : B.HasTorusApartmentCorrespondence) (g : rationalPoints G) :
    B.torusApartment (B.conjTorus g) = g • B.apartmentImage := by
  ext y
  constructor
  · rintro ⟨g', hg', hy⟩
    rwa [← (h.conjTorus_eq_iff g' g).1 hg']
  · intro hy
    exact ⟨g, rfl, hy⟩

/-- The apartment of an actual maximal split torus with a chart at `h` is `h · A(S)`. -/
theorem HasTorusApartmentCorrespondence.torusApartment_range {B : ValuationBuildingData G}
    (h : B.HasTorusApartmentCorrespondence) {T₂ : CommGroupScheme (Spec (CommRingCat.of F))}
    {i₂ : T₂.toGrp ⟶ G} {g : rationalPoints G} {σ : B.S ≅ T₂} (hc : B.IsTorusChart i₂ g σ) :
    B.torusApartment (SubgroupFunctor.range i₂) = g • B.apartmentImage := by
  rw [← hc.conjTorus_eq]
  exact h.torusApartment_conjTorus g

/-- Under the correspondence, `T ↦ B.torusApartment T` maps the maximal split tori bijectively
onto the apartments of `B(G)`. -/
theorem HasTorusApartmentCorrespondence.bijOn {B : ValuationBuildingData G}
    (h : B.HasTorusApartmentCorrespondence) :
    Set.BijOn B.torusApartment (maximalSplitTori G) {Y | B.IsApartment Y} := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨g, rfl⟩ := h.exists_conjTorus_eq T hT
    exact ⟨g, h.torusApartment_conjTorus g⟩
  · intro T hT T' hT' heq
    obtain ⟨g, rfl⟩ := h.exists_conjTorus_eq T hT
    obtain ⟨g', rfl⟩ := h.exists_conjTorus_eq T' hT'
    rw [h.torusApartment_conjTorus, h.torusApartment_conjTorus] at heq
    exact (h.conjTorus_eq_iff g g').2 heq
  · rintro Y ⟨g, rfl⟩
    exact ⟨B.conjTorus g, B.conjTorus_mem_maximalSplitTori g, h.torusApartment_conjTorus g⟩

/-! ### The polysimplicial structure -/

/-- A polysimplicial structure on `B(G)`: a polysimplicial complex `K = (B₁, …, Bₙ)`
(KP Definition 1.5.1(2)) with vertex set `V₁ × ⋯ × Vₙ`, and a bijection `realize` between the
facets of `K` and the facets of `B(G)` (`IntegralModels.BuildingFacet B`, the sets satisfying
`ValuationBuildingData.IsFacet`). These are data. The
validity clauses of KP Axiom 4.1.1 on them are in `SatisfiesBuildingAxiom`. -/
structure PolysimplicialRealization : Type (u + 1) where
  /-- The index set of the factors. -/
  index : Type u
  [finite : Finite index]
  /-- The vertex sets of the factors. -/
  V : index → Type u
  /-- The polysimplicial complex. -/
  complex : AbstractBuilding.PolysimplicialComplex index V
  /-- The facets of the complex are the facets of `B(G)`. -/
  realize : complex.facets ≃ BruhatTits.IntegralModels.BuildingFacet B

attribute [instance] PolysimplicialRealization.finite

namespace PolysimplicialRealization

variable {B} (R : B.PolysimplicialRealization)

/-- The facets of `K` realized inside a subset `Y` of `B(G)`. -/
def apartmentComplex (Y : Set B.ReducedBuilding) : Set (Set (∀ i, R.V i)) :=
  {Fc | ∃ h : Fc ∈ R.complex.facets, (R.realize ⟨Fc, h⟩).1 ⊆ Y}

/-- The apartments of `K`: the sets of facets realized inside an apartment `g · A(S)` of
`B(G)`. -/
def apartments : Set (Set (Set (∀ i, R.V i))) :=
  {𝒜 | ∃ Y, B.IsApartment Y ∧ 𝒜 = R.apartmentComplex Y}

/-- The realization matches faces: for facets `F, F'` of `K`, `F ⊆ F'` (`F` is a face of `F'`,
KP Definition 1.5.1(4)) if and only if the realized facets satisfy
`IntegralModels.FacetPrecedes`. -/
def IsFaceCompatible : Prop :=
  ∀ Fc Fc' : R.complex.facets,
    (Fc : Set (∀ i, R.V i)) ⊆ Fc' ↔
      BruhatTits.IntegralModels.FacetPrecedes B (R.realize Fc) (R.realize Fc')

/-- `G(F)` acts on `K` by polysimplicial automorphisms (KP Axiom 4.1.1 and Definition
1.5.1(13)): for every `g ∈ G(F)` there is a polysimplicial automorphism `e` of `K` such that `e`
maps a facet `F` of `K` to the facet `F'` exactly when `g` maps the realization of `F` to that of
`F'`. -/
def IsPolysimplicialAction : Prop :=
  ∀ g : rationalPoints G, ∃ e : (∀ i, R.V i) ≃ (∀ i, R.V i),
    AbstractBuilding.IsPolysimplicialAutomorphism R.complex e ∧
      ∀ Fc Fc' : R.complex.facets,
        (Fc' : Set (∀ i, R.V i)) = e '' Fc ↔
          (R.realize Fc').1 = (fun y : B.ReducedBuilding => g • y) '' (R.realize Fc).1

end PolysimplicialRealization

/-! ### The clauses of Axiom 4.1.1 for one group -/

/-- The clauses of KP Axiom 4.1.1 for the group `G`, on the reduced building `B(G)` of `B` and
a polysimplicial structure `R` on it:

* the facets of `K` and of `B(G)` correspond with their face relations (`faceCompatible`);
* `K`, with the apartments `R.apartments` coming from the apartments `g · A(S)` of `B(G)`, is a
  building in the sense of KP Definition 1.5.5 (`isBuilding`);
* `G(F)` acts on `K` by polysimplicial automorphisms (`polysimplicialAction`);
* the apartments are in bijective `G(F)`-equivariant correspondence with the maximal split tori
  (`torusApartmentCorrespondence`);
* the stabilizer of `A(S)` in `G(F)` is `N(F)` (`normalizerApartmentStabilizer`).

The comparisons for surjective homomorphisms with central kernel involve the buildings of two
groups and are not part of this one-group predicate. -/
structure SatisfiesBuildingAxiom (R : B.PolysimplicialRealization) : Prop where
  /-- The face relations of `K` and of `B(G)` agree under the realization. -/
  faceCompatible : R.IsFaceCompatible
  /-- `K` with its apartments is a building (KP Definition 1.5.5). -/
  isBuilding : AbstractBuilding.IsBuilding R.complex R.apartments
  /-- `G(F)` acts by polysimplicial automorphisms. -/
  polysimplicialAction : R.IsPolysimplicialAction
  /-- Apartments correspond bijectively and equivariantly to maximal split tori. -/
  torusApartmentCorrespondence : B.HasTorusApartmentCorrespondence
  /-- The stabilizer of `A(S)` in `G(F)` is `N(F)`. -/
  normalizerApartmentStabilizer : B.HasNormalizerApartmentStabilizer

end ValuationBuildingData

end Langlands.Geometry.Building
