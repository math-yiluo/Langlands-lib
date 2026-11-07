import Langlands.Representation.Exponents.StandardCompressionGeometry
import Langlands.Representation.Exponents.CuspidalCompressionReduction
import Langlands.Representation.Exponents.UniformCompressionReduction
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaFinitenessStatement

/-! # Uniform dynamic compression from named native and structural inputs

This conditional assembly does not prove its global input statements.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open Plancherel Plancherel.RationalNormalized CuspidalSupport

universe u v

/-- The precise remaining global inputs imply the unchanged uniform endpoint.
No input statement is asserted by this reduction. -/
def UniformCompressionNativeReductionStatement : Prop :=
  GenericMinimalParabolicStatement.{u} →
  ParabolicDynamicStatement.{u} →
  SmoothMaximalSplitTorusConjugacyStatement.{u} →
  StandardCocharacterStatement.{u} →
  StandardLeviIntersectionStatement.{u} →
  RelativeRootSystemStatement.{u} →
  BruhatTits.DynamicParabolicQuotientCompactStatement.{u} →
  RationalPointsIrreducibleAdmissibleStatement.{u, max u v} →
  RationalSupercuspidalJacquetFamilyFiniteStatement.{u, max u v} →
  RationalCuspidalInertiaProductDecompositionStatement.{u, max u v} →
  RationalCuspidalInertiaFinitenessStatement.{u, max u v} →
  RationalUniversalSmallProgeneratorStatement.{u, max u v} →
  RationalCuspidalInducedEmbeddingStatement.{u, max u v} →
  UniformCompressionStabilizationStatement.{u, v}

set_option maxHeartbeats 1200000 in
/-- Native coefficient finiteness, actual cuspidal decomposition and finite
embeddings, with the named structural inputs, give the exact uniform conclusion
at arbitrary independent field and carrier universes. -/
theorem uniformCompressionStabilization_of_nativeStatements
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, max u v})
    (hJac : RationalSupercuspidalJacquetFamilyFiniteStatement.{u, max u v})
    (hDecomp : RationalCuspidalInertiaProductDecompositionStatement.{u, max u v})
    (hFinite : RationalCuspidalInertiaFinitenessStatement.{u, max u v})
    (hGen : RationalUniversalSmallProgeneratorStatement.{u, max u v})
    (hEmbed : RationalCuspidalInducedEmbeddingStatement.{u, max u v}) :
    UniformCompressionStabilizationStatement.{u, v} := by
  apply uniformCompressionStabilizationStatement_iff_pointwise.mpr
  intro F _ _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ ξ K hK g hcentral hc
  classical
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot F G hG T i hi
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let h := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν
  let hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  let hM := isClosed_levi_of_isNonarchimedeanLocalField i ν
  let hInner := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
  apply pointwiseCompressionEventuallyStable_of_cuspidalInduced
    (parabolic i ν) (levi i ν) (unipotent i ν) h hU hM hInner K hK g
    (hEmbed F G hG T i hi ν hν hStandard hInter hRoots hU hM)
  intro I D hD
  obtain ⟨A, a, r⟩ :=
    standardCompressionRootPresentation i ν I hminimal hPD hStandard hG hi hν
  obtain ⟨_, hl, hn, _⟩ :=
    RepresentedParabolic.standard_representatives_geometric i ν hPD hStandard hG hi hν I
  let L := Standard.leviScheme i ν (rootSet i ν I)
  have hL : IsConnectedReductive L := hl.isConnectedReductive
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace F L
  let : NonarchimedeanGroup (rationalPoints L) := rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  let j := standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
  have hj : IsMaximalSplitTorus j :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have := hj.isSplitSubtorus.mono
  have hνL : IsGenericCocharacter j ν :=
    (standardLeviStandardFamilies dynamicLie hStandard F G hG T i hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I) L hL
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  have hRootsL : HasRelativeRootSystem j :=
    hRoots.of_standardLeviTorusFactor hStandard hG hi ν hν (rootSet i ν I)
      (rootSet_subset i ν I) hL (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  let := simpleRelativeRootFintype j hRootsL hj.isSplitSubtorus.1 ν
  let hOwn := isSemidirectDecomposition_of_standardCocharacterStatement
    j ν hStandard hL hj hνL
  let hUL := isClosed_unipotent_of_isNonarchimedeanLocalField j ν
  let hR := standardCompression_semidirect i ν I (h I)
  let hUR := standardCompression_radical_isClosed i ν I
  have hNative := standardCompression_nativeJacquetInputs_of_statements
    i ν I hR r hOwn hUL hUR hPD hconj hStandard hcompact hG hi hν hRoots hAdm hJac
  exact literalLeviInduction_eventuallyStable_of_nativeJacquet
    i ν I r h hU hR hUR hOwn hUL hL
    (continuous_standardCompression_projection i ν I hR hStandard hG hi hν)
    (compactSpace_standardCompression_leftQuotient i ν I hcompact hStandard hG hi hν)
    hn
    (hDecomp F L hL T j hj ν hνL hStandard hRootsL hUL)
    (hFinite F L hL T j hj ν hνL hStandard hRootsL hUL)
    (hGen F L hL T j hj ν hνL hStandard hRootsL hUL)
    hNative ξ K hK g hc hcentral (hM I) (hInner I)
    dynamicLie hStandard hG hi hν D hD

/-- The conditional reduction holds; the thirteen global input statements
remain premises of its application. -/
theorem uniformCompressionNativeReduction :
    UniformCompressionNativeReductionStatement.{u, v} :=
  uniformCompressionStabilization_of_nativeStatements

end Langlands.Aubert.General.RationalPointFamily
