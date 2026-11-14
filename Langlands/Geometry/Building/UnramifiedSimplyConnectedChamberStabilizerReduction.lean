import Langlands.Geometry.Building.IntegerChamberStabilizerReduction
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.AffineWeylFacetFixing
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylStatement
import Langlands.Geometry.Building.UnramifiedSimplyConnectedChamberStabilizerStatement

/-! # Chamber stabilizers from the simply connected normalizer image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- Containment of the actual normalizer image in the affine Weyl group implies
pointwise fixing of every apartment facet stabilized by a normalizer element. -/
theorem normalizer_facet_fixing_of_range_le_affineWeylGroup
    (hN : B.apartment.normalizerAffineEquiv.range ≤
      AffineRootSystem.affineWeylGroup B.affineRoots)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : normalizerPoints B.i) (hn : n • Fa = Fa) :
    ∀ x ∈ Fa, n • x = x := by
  let w : AffineRootSystem.affineWeylGroup B.affineRoots :=
    ⟨B.apartment.normalizerAffineEquiv n, hN ⟨n, rfl⟩⟩
  exact AffineRootSystem.affineWeyl_facet_fixing
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
      B.hasOppositeFactorPairs) hFa w hn

/-- With affine Weyl containment of the normalizer image, every setwise
stabilizer of any full facet of the original quotient fixes it pointwise. -/
theorem mem_pointwiseFixer_of_stabilizes_facet_of_range_le_affineWeylGroup
    (hN : B.apartment.normalizerAffineEquiv.range ≤
      AffineRootSystem.affineWeylGroup B.affineRoots)
    {Y : Set B.ReducedBuilding} (hY : B.IsFacet Y)
    (g : rationalPoints G) (hg : (g • ·) '' Y = Y) :
    g ∈ B.pointwiseFixer Y := by
  obtain ⟨h, Fa, hFa, rfl⟩ := hY
  obtain ⟨n, hn, heq⟩ :=
    B.exists_normalizer_stabilizes_eq_on_translated_facet hFa h g hg
  have hfix := B.normalizer_facet_fixing_of_range_le_affineWeylGroup hN hFa n hn
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer]
  rintro z ⟨x, hx, rfl⟩
  rw [heq x hx, hfix x hx]

end IntegerValuationBuildingData

namespace MaximalUnramified

/-- The full simply connected normalizer-image assertion implies the chamber
stabilizer assertion over the actual maximal unramified field. -/
def SimplyConnectedChamberStabilizerReductionStatement : Prop :=
  SimplyConnectedNormalizerAffineWeylStatement.{u} →
    SimplyConnectedChamberStabilizerStatement.{u}

/-- The reduction retains the normalizer-image proposition as its sole
unproved input. -/
theorem simplyConnectedChamberStabilizerReduction :
    SimplyConnectedChamberStabilizerReductionStatement.{u} := by
  intro hN F _ _ _ _ G _ hG C Y hY g hg
  have hfacet : C.IsFacet Y := by
    obtain ⟨h, Ca, hCa, rfl⟩ := hY
    exact ⟨h, Ca, hCa.isFacet, rfl⟩
  exact C.mem_pointwiseFixer_of_stabilizes_facet_of_range_le_affineWeylGroup
    (hN F G hG C).le hfacet g hg

end MaximalUnramified

end Langlands.Geometry.Building
