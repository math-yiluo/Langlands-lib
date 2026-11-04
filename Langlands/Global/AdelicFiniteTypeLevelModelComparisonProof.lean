import Langlands.Global.AdelicFiniteTypeLevelModelComparisonStatement
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.Global.AdelicLevelModelComparisonProof

/-! # Finite-type comparison over the actual Noetherian S-integer bases -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FunctionField k F] (S : Finset (AlgebraicCurve.Place k F))
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

theorem curvePlaceLevelModelPointMap_injective_of_locallyOfFiniteType
    [LocallyOfFiniteType X.hom] :
    Function.Injective (curvePlaceLevelModelPointMap k F S X) := by
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  let : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact curvePlaceLevelModelPointMap_injective k F S X

theorem curvePlaceLevelModelPointMap_bijective_of_finiteType
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Function.Bijective (curvePlaceLevelModelPointMap k F S X) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨curvePlaceLevelModelPointMap_injective_of_locallyOfFiniteType k F S X,
    curvePlaceLevelModelPointMap_surjective k F S X⟩

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

theorem numberFieldLevelModelPointMap_injective_of_locallyOfFiniteType
    [LocallyOfFiniteType X.hom] :
    Function.Injective (numberFieldLevelModelPointMap K S X) := by
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  let : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact numberFieldLevelModelPointMap_injective K S X

theorem numberFieldLevelModelPointMap_bijective_of_finiteType
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Function.Bijective (numberFieldLevelModelPointMap K S X) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨numberFieldLevelModelPointMap_injective_of_locallyOfFiniteType K S X,
    numberFieldLevelModelPointMap_surjective K S X⟩

end NumberField

theorem adelicFiniteTypeLevelModelComparison :
    AdelicFiniteTypeLevelModelComparisonStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S X
    constructor
    · intro hFiniteType
      exact curvePlaceLevelModelPointMap_injective_of_locallyOfFiniteType k F S X
    · intro hFiniteType hQuasiCompact
      exact curvePlaceLevelModelPointMap_bijective_of_finiteType k F S X
  · intro K _ _ S X
    constructor
    · intro hFiniteType
      exact numberFieldLevelModelPointMap_injective_of_locallyOfFiniteType K S X
    · intro hFiniteType hQuasiCompact
      exact numberFieldLevelModelPointMap_bijective_of_finiteType K S X

end Langlands.Global
