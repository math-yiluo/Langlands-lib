import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsStatement
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof
import Langlands.Geometry.Building.UnramifiedZeroNormalizerComparison
import Langlands.Geometry.Building.IntegerValuationSharpCoverImage
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # The zero group acts without inversions over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.MaximalUnramified

/-- An element of the zero subgroup cannot move an apartment point to a distinct
point of its own facet in the actual reduced-building quotient. -/
theorem zeroFacetNoInversions : ZeroFacetNoInversionsStatement.{u} := by
  intro F _ _ _ _ H _ C E x y g hy hg hgxy
  have hab :
      ApartmentQuotient.mk C.apartment.sharpFixerFamily (g, x) =
        ApartmentQuotient.mk C.apartment.sharpFixerFamily (1, y) := by
    have h :
        ApartmentQuotient.mk C.apartment.sharpFixerFamily (g * 1, x) =
          ApartmentQuotient.mk C.apartment.sharpFixerFamily (1, y) := hgxy
    simpa only [mul_one] using h
  obtain ⟨n, hnx, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff C.apartment.sharpFixerFamily g 1 x y).mp hab
  have hp' : g⁻¹ * (n : rationalPoints H) ∈ C.sharpFixer {x} := by
    change g⁻¹ * 1 * (n : rationalPoints H) ∈ C.apartment.sharpFixer {x} at hp
    simpa only [mul_one] using hp
  have hn : (n : rationalPoints H) ∈ E.zeroPoints := by
    have h1 := E.sharpFixer_le_zeroPoints C {x} hp'
    have h2 := E.zeroPoints.mul_mem hg h1
    simpa only [mul_inv_cancel_left] using h2
  let w : AffineRootSystem.affineWeylGroup C.affineRoots :=
    ⟨C.apartment.normalizerAffineEquiv n,
      E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints
        C simplyConnectedNormalizerAffineWeyl n hn⟩
  have hΨ := C.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    C.hasOppositeFactorPairs
  have hwx : (w : C.Apartment ≃ᵃ[ℝ] C.Apartment) x = y := by
    change C.apartment.normalizerAffineEquiv n x = y
    rw [KPApartmentData.normalizerAffineEquiv_apply, hnx]
  have hrel : AffineRootSystem.facetRel C.affineRoots x
      ((w : C.Apartment ≃ᵃ[ℝ] C.Apartment) x) := by
    rw [hwx]
    exact AffineRootSystem.mem_facet.mp hy
  have hfix := AffineRootSystem.eq_of_facetRel_apply hΨ w x hrel
  rw [hwx] at hfix
  exact hfix

end Langlands.Geometry.Building.MaximalUnramified
