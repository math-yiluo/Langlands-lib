import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.Geometry.Building.UnipotentIwahoriQuotientReduction
import Langlands.Geometry.Building.IwasawaDecompositionProof
import Langlands.Geometry.Building.UnipotentNormalizerCosetReduction
import Langlands.Geometry.Building.ChamberIwahoriLocalReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof

/-! # Proof of the unipotent Iwahori double-coset bijections (KP Theorem 7.8.1(4))

The published per-data assembly
`ParahoricBuildingData.unipotentIwahoriDoubleCosetBijection_of_iwasawa_coset` builds both
equivalences from the chamber Iwasawa decomposition and the corrected normalizer-coset
criterion. Iwasawa is the published `iwasawaDecomposition`. The coset criterion follows from
`unipotentNormalizerCoset_of_chamberIwahori`, using the normality of `Z(F)^0` in `N(F)` and
the chamber Iwahori decomposition, which are both available from published results.
-/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **KP Theorem 7.8.1(4), added in the 2024 corrections.** For every chamber `C` of the
apartment and every generic cocharacter `ν`, the maps `W̃^0 → U(F)\G(F)/P_C` and
`W̃^0 → U(F)Z(F)^0\G(F)/P_C`, `n ↦ U(F) n P_C` and `n ↦ U(F)Z(F)^0 n P_C`, are bijective. -/
theorem unipotentIwahoriDoubleCoset : UnipotentIwahoriDoubleCosetStatement.{u} := by
  intro F _ _ _ _ G _ P hH hk hP C ν hC hν
  have := P.normal_normalizerZero
  have hrank := rootRankOneFactorization F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus
  have hdec := P.chamberIwahoriDecomposition_of_rankOneFactorization hrank
    P.zeroDatum.coverImageCentralizerNormKernel RelativeRoot.dynamicRootOrderedProduct
  exact P.unipotentIwahoriDoubleCosetBijection_of_iwasawa_coset C ν
    (iwasawaDecomposition F G P hH hk hP C ν hC hν)
    (P.unipotentNormalizerCoset_of_chamberIwahori hdec hP C ν hC hν)

end Langlands.Geometry.Building
