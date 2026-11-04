import Langlands.GroupScheme.Torus.SplitPartCharacters
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge

/-! # Positive-power factorization through a torus's split part and norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom T.X.hom] [LocallyOfFiniteType T.X.hom]
  (i : A.toGrp ⟶ T.toGrp)

/-- The index of restriction to the split part; it is positive for a closed split subtorus. -/
def splitNormExponent : ℕ := (characterRestrict i).range.index

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem splitNormExponent_pos (hi : IsSplitSubtorus i) : 0 < splitNormExponent i := by
  have hindex := CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict i
    ⟨hi, isCentral_to_commGroupScheme i⟩
  exact Nat.pos_of_ne_zero hindex.index_ne_zero

/-- Every torus point has a fixed positive power equal to a split-part point
 times a point in the actual rational-character norm kernel. -/
theorem exists_split_mul_commonNormKernel (hT : IsTorus T.toGrp)
    (hi : IsMaximalSplitTorus i) (x : rationalPoints T.toGrp) :
    ∃ a : rationalPoints A.toGrp, ∃ z : rationalCommonNormKernel T.toGrp,
      x ^ splitNormExponent i = rationalPoints.map i a * (z : rationalPoints T.toGrp) := by
  let y : rationalCharacterValuationImage T.toGrp :=
    ⟨rationalCharacterValuation T.toGrp x, x, rfl⟩
  obtain ⟨a, ha⟩ := RenardCartan.pow_index_mem_splitValuationImage i hi.1.1
    (hi.characterRestrict_injective_of_isTorus hT) y
  have hv : rationalCharacterValuation T.toGrp (rationalPoints.map i a) =
      rationalCharacterValuation T.toGrp (x ^ splitNormExponent i) := by
    have h := congrArg Subtype.val ha
    change rationalCharacterValuation T.toGrp (rationalPoints.map i a) =
      (rationalCharacterValuation T.toGrp x) ^ (characterRestrict i).range.index at h
    simpa only [splitNormExponent, map_pow] using h
  let z := (rationalPoints.map i a)⁻¹ * x ^ splitNormExponent i
  have hz : z ∈ rationalCommonNormKernel T.toGrp := by
    rw [← rationalCharacterValuation_ker]
    change rationalCharacterValuation T.toGrp z = 1
    dsimp only [z]
    rw [map_mul, map_inv, hv, inv_mul_cancel]
  refine ⟨a, ⟨z, hz⟩, ?_⟩
  change x ^ splitNormExponent i = rationalPoints.map i a *
    ((rationalPoints.map i a)⁻¹ * x ^ splitNormExponent i)
  rw [mul_inv_cancel_left]

/-- Chosen actual factors, retaining their exact product and norm-kernel membership. -/
def splitNormFactorization (hT : IsTorus T.toGrp) (hi : IsMaximalSplitTorus i)
    (x : rationalPoints T.toGrp) :
    {p : rationalPoints A.toGrp × rationalCommonNormKernel T.toGrp //
      x ^ splitNormExponent i =
        rationalPoints.map i p.1 * (p.2 : rationalPoints T.toGrp)} :=
  let h := exists_split_mul_commonNormKernel i hT hi x
  ⟨(Classical.choose h, Classical.choose (Classical.choose_spec h)),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.Plancherel
