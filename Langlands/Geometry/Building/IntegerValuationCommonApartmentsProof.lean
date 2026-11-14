import Langlands.Geometry.Building.IntegerChamberGeneration
import Langlands.Geometry.Building.AffineWeylFacetFixing
import Langlands.Geometry.Building.IntegerValuationCommonApartments
import Langlands.Geometry.Building.ApartmentQuotientFactorization
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer

/-! # Common apartments for the actual integer-valued quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building
namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- Every rational point preserves the sharp chamber normalizer cover. -/
theorem sharpChamberCoverStabilizer_eq_top
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C) :
    B.apartment.sharpChamberCoverStabilizer C = ⊤ := by
  apply top_unique
  rw [← B.sharpFixer_sup_normalizer_eq_top hunit hC]
  exact sup_le (B.apartment.sharpFixer_le_sharpChamberCoverStabilizer C)
    (B.normalizer_le_sharpChamberCoverStabilizer hunit hC)

/-- Every original rational point has a sharp chamber-normalizer-chamber
factorization. -/
theorem mem_sharpChamberNormalizerCover
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C)
    (g : rationalPoints G) :
    g ∈ B.apartment.sharpChamberNormalizerCover C := by
  have hg : g ∈ B.apartment.sharpChamberCoverStabilizer C := by
    rw [B.sharpChamberCoverStabilizer_eq_top hunit hC]
    exact Subgroup.mem_top g
  have h1 := B.apartment.normalizer_mem_sharpChamberNormalizerCover C 1
  simpa only [mul_one] using hg.1 1 h1

/-- The sharp fixer of a facet is contained in the sharp fixer of any point
in its affine closure. -/
theorem sharpFixer_facet_le_singleton_of_mem_facetClosure
    {c x : B.Apartment} (hx : x ∈ AffineRootSystem.facetClosure B.affineRoots c) :
    B.apartment.sharpFixer (AffineRootSystem.facet B.affineRoots c) ≤
      B.apartment.sharpFixer {x} := by
  change (⨆ a : relativeRoots B.i,
    B.apartment.rootFixer a (AffineRootSystem.facet B.affineRoots c)) ≤ _
  refine iSup_le fun a g hg => B.apartment.rootFixer_le_sharpFixer a {x} ?_
  rw [B.apartment.rootFixer_singleton]
  exact (B.apartment.filtration_comparison_of_mem_facetClosure
    (fun _ h => B.mem_or_two_smul_mem_affineRoots h) hx a.property).2
    ((B.apartment.mem_rootFixer.mp hg).2 c (AffineRootSystem.mem_facet_self _ _))

/-- The full chamber cover transports to two possibly different endpoint
sharp fixers in the same original apartment. -/
theorem exists_sharpFixer_normalizer_sharpFixer_mul
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (x y : B.Apartment) (g : rationalPoints G) :
    ∃ p ∈ B.apartment.sharpFixer {x}, ∃ n : normalizerPoints B.i,
      ∃ q ∈ B.apartment.sharpFixer {y}, g = p * (n : rationalPoints G) * q := by
  have hsys := B.isAffineRootSystemWithRankZero_affineRoots hunit
  have hloc := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  obtain ⟨c, hc, hxc⟩ := hloc.exists_regularPoint_closure x
  obtain ⟨d, hd, hyd⟩ := hloc.exists_regularPoint_closure y
  have hC : AffineRootSystem.IsChamber B.affineRoots
      (AffineRootSystem.facet B.affineRoots c) := ⟨c, hc, rfl⟩
  have hD : AffineRootSystem.IsChamber B.affineRoots
      (AffineRootSystem.facet B.affineRoots d) := ⟨d, hd, rfl⟩
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity _ _ _ hsys _ _ hC hD
  obtain ⟨m, hm⟩ := B.affineWeylGroup_le_range w.property
  have hmC : m • AffineRootSystem.facet B.affineRoots c =
      AffineRootSystem.facet B.affineRoots d := by
    change (B.apartment.normalizerAffineEquiv m : B.Apartment → B.Apartment) '' _ = _
    rw [hm]
    exact hw
  obtain ⟨p, hp, n, q, hq, hg⟩ :=
    B.mem_sharpChamberNormalizerCover hunit hC (g * (m : rationalPoints G))
  have hq' := B.apartment.sharpFixer_le_comap m
    (AffineRootSystem.facet B.affineRoots c) hq
  change (m : rationalPoints G) * q * (m : rationalPoints G)⁻¹ ∈
    B.apartment.sharpFixer (m • AffineRootSystem.facet B.affineRoots c) at hq'
  rw [hmC] at hq'
  refine ⟨p, B.sharpFixer_facet_le_singleton_of_mem_facetClosure hxc hp,
    n * m⁻¹, (m : rationalPoints G) * q * (m : rationalPoints G)⁻¹,
    B.sharpFixer_facet_le_singleton_of_mem_facetClosure hyd hq', ?_⟩
  have hg' := congrArg (fun z : rationalPoints G => z * (m : rationalPoints G)⁻¹) hg
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc
    g = (p * (n : rationalPoints G) * q) * (m : rationalPoints G)⁻¹ := by
      simpa only [mul_inv_cancel_right] using hg'
    _ = _ := by group

/-- The original sharp-fixer quotient has common translated apartments for
integer-valued data with an order-one unit. -/
theorem hasCommonApartments
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) :
    B.apartment.HasCommonApartments := by
  apply (ApartmentQuotient.hasCommonTranslatedApartment_iff_factorization
    B.apartment.sharpFixerFamily).mpr
  exact B.exists_sharpFixer_normalizer_sharpFixer_mul hunit

end IntegerValuationBuildingData

namespace MaximalUnramified

/-- Every two points in the actual maximal-unramified quotient lie in one
translated original apartment, at every universe. -/
theorem commonApartments : CommonApartmentsStatement.{u} := by
  intro F _ _ _ _ G _ B
  exact B.hasCommonApartments (exists_order_eq_one F)

end MaximalUnramified
end Langlands.Geometry.Building
