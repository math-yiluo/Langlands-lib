import Langlands.Geometry.Building.AffineBoundedFacetFiniteness
import Langlands.Geometry.Building.ApartmentFacetVertexInvariance
import Langlands.Geometry.Building.IntegerFiniteFixerAction
import Langlands.Geometry.Building.IntegerFacetVertexFixingStatement
import Langlands.Geometry.Building.AffineRootDoubling
import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Finite vertex approximation from closed-facet fixation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

local instance : Fintype (relativeRoots B.i) := by
  letI := B.isConnectedReductive.smooth
  exact (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).fintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- The exact finite image of all vertices of closed apartment facets meeting
the bounded set, in the apartment translated by `g`. -/
def facetClosureVertexFinset
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (g : rationalPoints G) (Ω : Set B.Apartment)
    (hΩ : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    Finset B.ReducedBuilding := by
  classical
  exact (AffineRootSystem.boundedFacetVertexFinset hΨ Ω hΩ).image
    (fun q => g • B.apartmentMap q)

@[simp] theorem mem_facetClosureVertexFinset
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (g : rationalPoints G) (Ω : Set B.Apartment)
    (hΩ : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (y : B.ReducedBuilding) :
    y ∈ B.facetClosureVertexFinset hΨ g Ω hΩ ↔
      y ∈ B.apartment.facetClosureVertexImage g Ω := by
  classical
  simp only [facetClosureVertexFinset, Finset.mem_image,
    AffineRootSystem.mem_boundedFacetVertexFinset,
    KPApartmentData.facetClosureVertexImage, Set.mem_image, Set.mem_ofPred_eq]

theorem facetClosureVertexFinset_nonempty
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (g : rationalPoints G) {Ω : Set B.Apartment}
    (hΩ : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) (hne : Ω.Nonempty) :
    (B.facetClosureVertexFinset hΨ g Ω hΩ).Nonempty := by
  classical
  exact (AffineRootSystem.boundedFacetVertexFinset_nonempty hΨ hΩ hne).image _

theorem isVertex_of_mem_facetClosureVertexFinset
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (g : rationalPoints G) (Ω : Set B.Apartment)
    (hΩ : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    {y : B.ReducedBuilding}
    (hy : y ∈ B.facetClosureVertexFinset hΨ g Ω hΩ) : B.IsVertex y := by
  obtain ⟨q, ⟨p, hp, hq, hv⟩, rfl⟩ :=
    (B.mem_facetClosureVertexFinset hΨ g Ω hΩ y).mp hy
  exact ⟨g, q, rfl, hv⟩

/-- AS4 for the supplied integer-valuation building data follows from actual
rank-one factorization, without a further building-axiom assumption. -/
theorem extendedAffineRoot_mem_or_two_smul_mem
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots := by
  let := B.isConnectedReductive.smooth
  have hrank := rootRankOneFactorization k G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus
  exact B.apartment.mem_or_two_smul_mem_affineRoots_of_oppositePairs
    B.isMaximalSplitTorus.isSplitSubtorus.1
    (fun a ha h hh h1 => (hrank a ha h hh h1).1.exists) hψ

/-- The norm-one pointwise fixer of the original translated subset preserves
the exact finite vertex set. -/
theorem smul_mem_facetClosureVertexFinset
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (g : rationalPoints G) (Ω : Set B.Apartment)
    (hΩ : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    {h : rationalPoints G}
    (hh : h ∈ B.pointwiseFixer ((fun x => g • B.apartmentMap x) '' Ω))
    {y : B.ReducedBuilding}
    (hy : y ∈ B.facetClosureVertexFinset hΨ g Ω hΩ) :
    h • y ∈ B.facetClosureVertexFinset hΨ g Ω hΩ := by
  rw [B.mem_facetClosureVertexFinset] at hy ⊢
  exact B.apartment.smul_mem_facetClosureVertexImage
    (fun _ hψ => B.extendedAffineRoot_mem_or_two_smul_mem hψ) g Ω hh hy

/-- Closed-facet vertex fixation supplies the missing containment; the actual
permutation action on the finite vertex set supplies normality and finite index. -/
theorem finiteVertexFixerApproximation_of_closedFacetsFixedByVertices
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hfacet : B.ClosedFacetsFixedByVertices)
    (g : rationalPoints G) (Ω : Set B.Apartment)
    (hne : Ω.Nonempty)
    (hΩ : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    ∃ Y : Finset B.ReducedBuilding,
      Y.Nonempty ∧ (∀ y ∈ Y, B.IsVertex y) ∧
      let U : Subgroup (rationalPoints G) := ⨅ y ∈ Y, B.oneStabilizer y
      let H := characterValuationKernel v G ⊓
        B.pointwiseFixer ((fun x => g • B.apartmentMap x) '' Ω)
      U ≤ H ∧ (U.subgroupOf H).Normal ∧ (U.subgroupOf H).FiniteIndex := by
  let Y := B.facetClosureVertexFinset hΨ g Ω hΩ
  have hYne : Y.Nonempty := B.facetClosureVertexFinset_nonempty hΨ g hΩ hne
  let H := characterValuationKernel v G ⊓
    B.pointwiseFixer ((fun x => g • B.apartmentMap x) '' Ω)
  have hYinv : ∀ h : H, ∀ y ∈ Y, (h : rationalPoints G) • y ∈ Y := by
    intro h y hy
    exact B.smul_mem_facetClosureVertexFinset hΨ g Ω hΩ h.property.2 hy
  refine ⟨Y, hYne, (fun _ hy =>
    B.isVertex_of_mem_facetClosureVertexFinset hΨ g Ω hΩ hy), ?_,
    B.normal_finiteIndex_iInf_oneStabilizer H Y inf_le_left hYinv⟩
  intro h hh
  rw [B.iInf_oneStabilizer_eq Y hYne] at hh
  refine ⟨hh.1, B.apartment.mem_pointwiseFixer.mpr ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hvertices : ∀ q : B.Apartment,
      q ∈ AffineRootSystem.facetClosure B.affineRoots p →
      AffineRootSystem.IsVertex B.affineRoots q →
      (g⁻¹ * h * g) • B.apartmentMap q = B.apartmentMap q := by
    intro q hq hv
    have hqY : g • B.apartmentMap q ∈ Y :=
      (B.mem_facetClosureVertexFinset hΨ g Ω hΩ _).mpr
        ⟨q, ⟨p, hp, hq, hv⟩, rfl⟩
    have hfix := B.apartment.mem_pointwiseFixer.mp hh.2 _ hqY
    rw [mul_smul, mul_smul, hfix, inv_smul_smul]
  have hfixp := hfacet p (g⁻¹ * h * g) hvertices p
    (AffineRootSystem.mem_facetClosure_self B.affineRoots p)
  have heq := congrArg (g • ·) hfixp
  simpa only [mul_smul, smul_inv_smul] using heq

end Langlands.Geometry.Building.IntegerValuationBuildingData
