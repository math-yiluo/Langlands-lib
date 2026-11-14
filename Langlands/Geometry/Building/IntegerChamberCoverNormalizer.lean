import Langlands.Geometry.Building.GenericChamberCoverAction
import Langlands.Geometry.Building.IntegerValuationExtendedAffineRoots

/-! # Actual simple lifts and normalizer invariance for integer-valued data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- Every actual affine root reflection has a normalizer lift negating the
relative root which is its derivative. -/
theorem exists_affineRootReflectionLift
    {psi : B.Apartment →ᵃ[ℝ] ℝ} (hpsi : psi ∈ B.affineRoots)
    {w : TranslationSpace B.i} (hw : AffineRootSystem.IsCoroot B.affineRoots psi w) :
    ∃ r : normalizerPoints B.i, ∃ a : relativeRoots B.i,
      psi.linear = rootForm B.i a ∧
      B.apartment.normalizerAffineEquiv r = AffineRootSystem.affineReflection psi hw.1 ∧
      weylAction B.i r a = -(a : characterLattice B.S) := by
  have hpsi' := B.apartment.affineRoots_subset_extendedAffineRoots hpsi
  rw [← B.reflectionAffineRoots_eq] at hpsi'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hpsi'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  refine ⟨B.reflectionElement hp, a, rfl, ?_, ?_⟩
  · have heq := B.reflectionCoroot_eq_of_isCoroot hg hg1 hp hw
    simpa only [heq] using B.normalizerAffineEquiv_reflectionElement hg hg1 hp
  · obtain ⟨hnu, hweyl⟩ := hp.coroot_spec B.i
      B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1
    change weylAction B.i (⟨p.1 * g * p.2, hp.2.2⟩ : normalizerPoints B.i) a = -a
    rw [hweyl, hnu]
    module

/-- A chosen actual lift of the specified affine root reflection, retaining
the derivative and its Weyl-negation property as a specification. -/
def affineRootReflectionLift
    (psi : B.Apartment →ᵃ[ℝ] ℝ) (hpsi : psi ∈ B.affineRoots)
    (w : TranslationSpace B.i) (hw : AffineRootSystem.IsCoroot B.affineRoots psi w) :
    normalizerPoints B.i :=
  (B.exists_affineRootReflectionLift hpsi hw).choose

theorem affineRootReflectionLift_spec
    (psi : B.Apartment →ᵃ[ℝ] ℝ) (hpsi : psi ∈ B.affineRoots)
    (w : TranslationSpace B.i) (hw : AffineRootSystem.IsCoroot B.affineRoots psi w) :
    ∃ a : relativeRoots B.i,
      psi.linear = rootForm B.i a ∧
      B.apartment.normalizerAffineEquiv (B.affineRootReflectionLift psi hpsi w hw) =
        AffineRootSystem.affineReflection psi hw.1 ∧
      weylAction B.i (B.affineRootReflectionLift psi hpsi w hw) a =
        -(a : characterLattice B.S) :=
  (B.exists_affineRootReflectionLift hpsi hw).choose_spec

/-- Every actual normalizer point preserves the sharp chamber normalizer cover,
for integer-valued data with an order-one unit. -/
theorem normalizer_le_sharpChamberCoverStabilizer
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C) :
    normalizerPoints B.i ≤ B.apartment.sharpChamberCoverStabilizer C := by
  apply B.apartment.normalizer_le_sharpChamberCoverStabilizer_of_simple_lifts
    (B.isAffineRootSystemWithRankZero_affineRoots hunit) hC
  rintro s ⟨psi, hpsi, w, hw, hs⟩
  let r := B.affineRootReflectionLift psi hpsi.1.1 w hw
  obtain ⟨a, hwall, hr, hra⟩ := B.affineRootReflectionLift_spec psi hpsi.1.1 w hw
  refine ⟨r, ?_, hr.trans hs.symm⟩
  exact B.apartment.reflection_mem_sharpChamberCoverStabilizer
    B.isConnectedReductive B.isMaximalSplitTorus
    (B.isAffineRootSystemWithRankZero_affineRoots hunit)
    (B.isAffineRootSystemWithRankZero_extendedAffineRoots hunit)
    B.derivativeRoots_extendedAffineRoots (fun _ h => B.mem_or_two_smul_mem_affineRoots h)
    hpsi hwall hw r hr hra

end Langlands.Geometry.Building.IntegerValuationBuildingData
