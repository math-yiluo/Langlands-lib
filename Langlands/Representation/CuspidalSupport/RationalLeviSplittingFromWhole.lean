import Langlands.Representation.Aubert.General.RationalLeviCuspidalRemainderTransport
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-!
# Literal Levi splittings from the closed whole-category statement

All actual-group structural and topology inputs are discharged here. The
whole-category theorem and the intrinsic Levi root-system input remain explicit.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The closed whole-category statement supplies a literal Levi splitting
whenever the intrinsic Levi torus has the required relative root system. -/
def RationalLeviCuspidalSplittingFromWholeStatement : Prop :=
  ∀ (_hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, v})
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (_hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u}),
    have := hG.isAffineHom
    have := hi.isSplitSubtorus.mono
    let : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (hν : IsGenericCocharacter i ν)
      (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))
      (I : Finset (SimpleRoot i ν))
      (hMI : IsClosed (levi i ν I : Set (rationalPoints G))),
      have : IsAffineHom (Standard.leviScheme i ν (rootSet i ν I)).X.hom :=
        (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)).isAffineHom
      have := (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν I)
        (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
        (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).isSplitSubtorus.mono
      ∀ (_hRootsL : HasRelativeRootSystem
        (standardLeviTorusFactor i ν (rootSet i ν I)
          (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))))
        (A : SmoothRep.{0, u, v} ℂ (levi i ν I)),
        HasLeviCuspidalRemainderSplitting
          (parabolic i ν) (levi i ν) (unipotent i ν) hU I hMI
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) A

/-- Apply the closed whole-category theorem to the represented standard Levi
and transport its actual coproduct to the literal Levi subgroup. -/
theorem hasLeviCuspidalRemainderSplitting_of_wholeStatement :
    RationalLeviCuspidalSplittingFromWholeStatement.{u, v} := by
  intro hwhole k _ _ _ _ G hG T i hi ν hStandard hInter
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  dsimp only
  intro _ _ hν hU I hMI hRootsL A
  let L := Standard.leviScheme i ν (rootSet i ν I)
  have hL : IsConnectedReductive L :=
    standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive
      hG hi hν I
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : TopologicalSpace (rationalPoints L) := pointTopology
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace k L
  let : NonarchimedeanGroup (rationalPoints L) :=
    Plancherel.rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space k L
  let iL := standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have := hiL.isSplitSubtorus.mono
  have hνL : IsGenericCocharacter iL ν :=
    (standardLeviStandardFamilies dynamicLie hStandard k G hG T i hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I) L hL
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  let := simpleRelativeRootFintype iL hRootsL hiL.isSplitSubtorus.1 ν
  let hUL := isClosed_unipotent_of_isNonarchimedeanLocalField iL ν
  have hdecomp := hwhole k L hL T iL hiL ν hνL hStandard hRootsL hUL
  exact hasLeviCuspidalRemainderSplitting_of_rationalWholeCoproduct
    i ν dynamicLie hStandard hG hi hν I hL hU hUL hMI
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      iL ν hStandard hL hiL hνL) hdecomp.1 A

end Langlands.Aubert.General.RationalPointFamily
