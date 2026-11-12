import Langlands.Representation.Plancherel.RationalCentralQuotient
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Rational.SplitComponentProof

/-! # Finite index of the actual norm kernel joined with the centre -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u

/-- The actual common norm kernel joined with the centre of the rational-point
group has finite index. The finite index comes from an actual split component. -/
theorem rationalCommonNormKernel_sup_center_finiteIndex
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    (Plancherel.rationalCommonNormKernel G ⊔
      Subgroup.center (GroupScheme.rationalPoints G)).FiniteIndex := by
  obtain ⟨A, s, hs⟩ := (GroupScheme.splitComponentStatement F G hG).1
  have hindex : (Plancherel.RenardCartan.splitValuationImage s).FiniteIndex :=
    Plancherel.RenardCartan.finiteIndex_splitValuationImage_of_injective hG s hs
      (GroupScheme.characterRestriction F G hG A s hs).1
  have := Plancherel.finite_rationalCentralQuotient s hs.isCentralSplitTorus.isCentral hindex
  have : (Plancherel.rationalCommonNormKernel G ⊔
      (GroupScheme.rationalPoints.map s).range).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le
    (sup_le_sup_left hs.isCentralSplitTorus.range_le_center _)

end Langlands.CuspidalSupport
