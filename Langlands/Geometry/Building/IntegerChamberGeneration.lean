import Langlands.Geometry.Building.IntegerChamberCoverNormalizer
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.RootGeneratedSubgroup

/-! # Generation by the actual chamber sharp fixer and normalizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- A centralizer conjugate of every root point belongs to the sharp chamber
root fixer, using only V6 and a unit of order one. -/
theorem exists_centralizer_conj_mem_rootFixer
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C)
    (a : relativeRoots B.i) {g : rationalPoints G} (hg : g ∈ rootGroupPoints B.i a) :
    ∃ z : rationalPoints B.centralizer.Z,
      (rationalPoints.map B.centralizer.j z)⁻¹ * g *
        rationalPoints.map B.centralizer.j z ∈ B.apartment.rootFixer a C := by
  by_cases hg1 : g = 1
  · subst g
    exact ⟨1, by simp⟩
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1
    (mt (x.isValuation.eq_top_iff a a.property g hg).1 hg1)
  obtain ⟨t, ht⟩ := hunit
  obtain ⟨z, hz⟩ := B.exists_centralizer_eval_translation_eq_neg_two t ht a
  obtain ⟨n, hn⟩ := exists_nat_ge (-r / 2)
  let w := z⁻¹ ^ n
  have hw : eval B.S a (B.translation w).toAdd = (n : ℝ) * 2 := by
    simp only [w, map_pow, toAdd_pow, map_nsmul, map_inv, toAdd_inv, map_neg,
      hz, nsmul_eq_mul]
    ring
  have hval := B.isOmegaCompatible x.val x.mem a a.property w g hg
  change x.val a ((rationalPoints.map B.centralizer.j w)⁻¹ * g *
      rationalPoints.map B.centralizer.j w) =
    x.val a g + ((eval B.S a (B.translation w).toAdd : ℝ) : WithTop ℝ) at hval
  have hroot : (rationalPoints.map B.centralizer.j w)⁻¹ * g *
      rationalPoints.map B.centralizer.j w ∈ rootGroupPoints B.i a := by
    have H := conj_mem_rootGroupPoints (B.centralizer.toNormalizer w⁻¹) hg
    simpa only [weylAction_centralizerToNormalizer B.centralizer.isRepresentedBy,
      inv_one, LinearEquiv.coe_one, id, Subgroup.coe_inv, coe_centralizerToNormalizer,
      map_inv, inv_inv] using H
  refine ⟨w, ?_⟩
  rw [(B.apartment.rootFixer_eq_filtration_of_isFacet
    (fun _ h => B.mem_or_two_smul_mem_affineRoots h) hC.isFacet hx a.property).1]
  apply KPApartmentData.mem_filtration.mpr
  refine ⟨hroot, ?_⟩
  rw [hval, ← hr, hw, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

/-- Every actual relative-root group lies in the join of the chamber sharp
fixer and the full actual normalizer. -/
theorem rootGroup_le_sharpFixer_sup_normalizer
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C)
    (a : relativeRoots B.i) :
    rootGroupPoints B.i a ≤ B.apartment.sharpFixer C ⊔ normalizerPoints B.i := by
  intro g hg
  obtain ⟨z, hz⟩ := B.exists_centralizer_conj_mem_rootFixer hunit hC a hg
  let K := B.apartment.sharpFixer C ⊔ normalizerPoints B.i
  have hzK : rationalPoints.map B.centralizer.j z ∈ K :=
    Subgroup.mem_sup_right (B.centralizer.toNormalizer z).property
  have hgK : (rationalPoints.map B.centralizer.j z)⁻¹ * g *
      rationalPoints.map B.centralizer.j z ∈ K :=
    Subgroup.mem_sup_left (B.apartment.rootFixer_le_sharpFixer a C hz)
  have H := K.mul_mem (K.mul_mem hzK hgK) (K.inv_mem hzK)
  convert H using 1
  group

/-- The identity inclusion of an actual root group into the join generated
by the chamber sharp fixer and the full actual normalizer. -/
def rootGroupChamberNormalizerInclusion
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C)
    (a : relativeRoots B.i) :
    rootGroupPoints B.i a →*
      ↥(B.apartment.sharpFixer C ⊔ normalizerPoints B.i) :=
  Subgroup.inclusion (B.rootGroup_le_sharpFixer_sup_normalizer hunit hC a)

/-- The chamber sharp fixer and the full actual normalizer generate all
rational points of the original group. -/
theorem sharpFixer_sup_normalizer_eq_top
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {C : Set B.Apartment} (hC : AffineRootSystem.IsChamber B.affineRoots C) :
    B.apartment.sharpFixer C ⊔ normalizerPoints B.i = ⊤ := by
  let := B.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ := B.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B.i
  let K := B.apartment.sharpFixer C ⊔ normalizerPoints B.i
  have hU : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ B.i) ≤ K := by
    apply RelativeRoot.dynamicUnipotent_le_of_disjoint_positive_rays
      B.isConnectedReductive B.isMaximalSplitTorus ν
    · intro a ha b hb hne
      exact B.hasOppositeFactorPairs.disjoint_cyclicTail_indivisibleRoots B.i
        B.isMaximalSplitTorus.isSplitSubtorus.1 ha.1 hb.1 hne
    · exact B.rootGroup_le_sharpFixer_sup_normalizer hunit hC
  apply top_unique
  intro g _
  obtain ⟨a, b, n, z, rfl⟩ := exists_unipotent_normalizer_unipotent_centralizer_mul B.i ν
    (genericCentralizer k G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus ν hν)
    (rationalBruhat k G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus ν hν) g
  exact K.mul_mem (K.mul_mem (K.mul_mem (hU a.property)
    (Subgroup.mem_sup_right n.property)) (hU b.property))
    (Subgroup.mem_sup_right (centralizerPoints_le_normalizerPoints B.i z.property))

end Langlands.Geometry.Building.IntegerValuationBuildingData
