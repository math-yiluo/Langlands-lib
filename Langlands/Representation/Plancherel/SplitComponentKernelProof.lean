import Langlands.Representation.Plancherel.RenardLatticeComparisonStatement
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex

/-! # The norm kernel of a split component (Renard V.2.6, Lemma)

The actual norm kernel of a connected reductive group pulls back along a split
component `s : T ⟶ Z` to the norm kernel of `T`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- If the restriction of rational characters along `s` has finite-index range, a point of `T`
whose image lies in the norm kernel of `Z` lies in the norm kernel of `T`. -/
theorem comap_rationalCommonNormKernel_le_of_finiteIndex (s : T.toGrp ⟶ Z)
    (hindex : (characterRestrict s).range.FiniteIndex) :
    (rationalCommonNormKernel Z).comap (rationalPoints.map s) ≤
      rationalCommonNormKernel T.toGrp := by
  intro t ht
  rw [Subgroup.mem_comap, mem_rationalCommonNormKernel_iff_valuation] at ht
  rw [mem_rationalCommonNormKernel_iff_valuation]
  intro χ
  have hn : (characterRestrict s).range.index ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  obtain ⟨ψ, hψ⟩ := AddSubgroup.nsmul_index_mem (characterRestrict s).range χ
  have h := rationalCharacterValuation_characterRestrict s ψ t
  rw [hψ, map_nsmul, ht ψ] at h
  exact (smul_eq_zero.mp h).resolve_left hn

/-- The pullback of the norm kernel along a finite-index restriction is the norm kernel. -/
theorem comap_rationalCommonNormKernel_eq_of_finiteIndex (s : T.toGrp ⟶ Z)
    (hindex : (characterRestrict s).range.FiniteIndex) :
    (rationalCommonNormKernel Z).comap (rationalPoints.map s) =
      rationalCommonNormKernel T.toGrp :=
  le_antisymm (comap_rationalCommonNormKernel_le_of_finiteIndex s hindex)
    (rationalCommonNormKernel_le_comap s)

/-- Renard V.2.6, Lemma: for an actual split component `s : T ⟶ Z` of an actual connected
reductive group over a nonarchimedean local field, the norm kernel of `Z` pulls back along `s`
to the norm kernel of `T` (`⁰A_G = ⁰G ∩ A_G`). -/
theorem splitComponentKernel : SplitComponentKernelStatement.{u} := by
  intro F _ _ _ _ Z hZ T s hs
  exact comap_rationalCommonNormKernel_eq_of_finiteIndex s
    (hs.finiteIndex_range_characterRestrict hZ)

end Langlands.Plancherel.RenardCartan
