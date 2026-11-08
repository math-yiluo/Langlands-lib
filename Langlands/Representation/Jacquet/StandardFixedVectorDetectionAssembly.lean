import Langlands.Representation.Jacquet.StandardNormalizedJacquetDetection
import Langlands.Representation.Jacquet.StandardFixedVectorStructure
import Langlands.Representation.Jacquet.FixedVectorUniverseLift
import Langlands.Representation.Jacquet.StandardFixedVectorSubquotientGenerationStatement
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.Representation.Smooth.FixedVectors.DetectionConsequencesProof
import Langlands.GroupScheme.Rational.StandardCocharacterReduction
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Standard fixed-vector detection without fixed-dimension bounds -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact

set_option maxHeartbeats 800000 in
/-- Literal inside-Levi cuspidality yields compact coefficients on the
intrinsic common norm kernel of the actual standard Levi scheme. -/
theorem leviCompactCoefficients_of_specialVertexInputs
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hInputs : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν) :
    have := hG.isAffineHom
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (hU : ∀ J, IsClosed (unipotent i ν J : Set (rationalPoints G)))
      (I : Finset (SimpleRoot i ν)) (hMI : IsClosed (levi i ν I : Set (rationalPoints G))),
      let L := Standard.leviScheme i ν (rootSet i ν I)
      ∀ (hL : IsConnectedReductive L),
        have := hL.isAffineHom
        have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
        let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
        let := hMI.locallyCompactSpace
        ∀ E : SmoothRep.{0, u, v} ℂ (levi i ν I),
          IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I hMI
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) E →
          HasCompactSmoothDualCoefficients
            (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel L)
              (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) E)).representation := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ _ _ hU I hMI L hL
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace F L
  let : NonarchimedeanGroup (rationalPoints L) :=
    Plancherel.rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  let := hMI.locallyCompactSpace
  intro _ _ _ _ E hE
  let iL := standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have := hiL.isSplitSubtorus.mono
  have hνL : IsGenericCocharacter iL ν :=
    (standardLeviStandardFamilies dynamicLie hStandard F G hG T i hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I) L hL
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  have hRootsL := hRoot F L hL T iL hiL
  let := simpleRelativeRootFintype iL hRootsL hiL.isSplitSubtorus.1 ν
  let hUL := isClosed_unipotent_of_isNonarchimedeanLocalField iL ν
  have hEcusp := (rationalLeviCuspidalityTransport dynamicLie hStandard
    F G hG T i hi ν hν I hL hU hUL hMI
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I)
    (isSemidirectDecomposition_of_standardCocharacterStatement iL ν hStandard hL hiL hνL)
    E).mpr hE
  obtain ⟨Dgeom, x, hspecial, hprops, hbasis, hcover⟩ :=
    hInputs F L hL T iL hiL ν hνL
  exact rationalCuspidalCompactRestriction F L hL T iL hiL ν hνL hStandard hRootsL
    hUL Dgeom x hspecial hprops hbasis hcover
    (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) E) hEcusp


end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Jacquet

open GroupScheme BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily

/-- Root-system existence, together with the proved sign comparisons, supplies
all standard-Levi intersection comparisons used by the detection argument. -/
theorem standardLeviIntersection_of_relativeRootSystem
    (hRoot : RelativeRootSystemStatement.{u}) : StandardLeviIntersectionStatement.{u} := by
  have hStandard := standardCocharacterStatement_of_relativeRootSystem_of_signs
    hRoot relativeRootSignsDetermineDynamic
  have hOrder : StandardParabolicOrderStatement.{u} := by
    intro F _ G hG T i hi ν
    have := hG.isAffineHom
    have := hi.isSplitSubtorus.mono
    intro hν
    exact standardParabolic_order_of_root_comparison i ν hν
      (relativeRootNegation F G hG T i hi)
      (fun J hJ => (hStandard F G hG T i hi ν hν J hJ).1)
      (fun z e => (relativeRootSignInclusions F G hG T i hi z e).1)
      (fun z e => (relativeRootSignInclusions F G hG T i hi z e).2)
  exact standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder
    hStandard hOrder

set_option maxHeartbeats 1600000 in
/-- Detect a nonzero fixed vector in every nonzero actual subquotient. The
four global prerequisites remain explicit; no fixed-space dimension is used. -/
theorem standardSubquotient_nonzero_fixed_of_prerequisites
    (hRoot : RelativeRootSystemStatement.{u})
    (hInputs : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u})
    (hJacquet : GeneralizedJacquetLemmaStatement.{u, max (u + 1) v})
    (hFinite : CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, max (u + 1) v}) :
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
        (_hν : IsGenericCocharacter i ν)
        (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν,
          ∃ zeta, IsStandardCocharacter i ν J zeta)
        (K0 : Subgroup (rationalPoints G))
        (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
          ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K0, g = m * n * k)
        (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
        (_hnormal : K0 ≤ Subgroup.normalizer K.toSubgroup)
        (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
          ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ T.toGrp),
            IsCompatibleStandardSplitComponent i ν J A q ∧
              StandardParabolicBasisMember i ν J q K.toSubgroup)
        (V : SmoothRep.{0, u, v} ℂ (rationalPoints G))
        (_hgen : ∀ S : Subrepresentation V.representation,
          fixedVectors V.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
        (D : SmoothRep.{0, u, v} ℂ (rationalPoints G))
        (_hDA : SmoothRep.IsSubquotient D V) (_hD : Nontrivial D),
        ∃ w : D, w ∈ fixedVectors D.representation K.toSubgroup ∧ w ≠ 0 := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  intro T i hi ν hν hstandard K0 hIwasawa K hK hnormal hIwahori V hgen D hDA hD
  classical
  have := hi.isSplitSubtorus.mono
  have hStandard := standardCocharacterStatement_of_relativeRootSystem_of_signs
    hRoot relativeRootSignsDetermineDynamic
  have hInter := standardLeviIntersection_of_relativeRootSystem hRoot
  have hRoots := hRoot F G hG T i hi
  let V' := SmoothRep.universeLift.{u + 1} V
  let D' := SmoothRep.universeLift.{u + 1} D
  let : Nontrivial D := hD
  let : Nontrivial D' := (SmoothRep.universeLiftEquiv D).toLinearEquiv.symm.toEquiv.nontrivial
  have hgen' : fixedVectorGenerated K.toSubgroup V' :=
    (fixedVectorGenerated_universeLift_iff K.toSubgroup V).mpr hgen
  have hDA' : SmoothRep.IsSubquotient D' V' := hDA.universeLift
  let hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  let hM := isClosed_levi_of_isNonarchimedeanLocalField i ν
  obtain ⟨I, -, E, hE, hEcusp, hEJ⟩ :=
    exists_irreducible_cuspidal_jacquet_subquotient
      i ν hStandard hInter hRoots hG hi hν hU hM D'
  obtain ⟨zeta, hzeta⟩ := hstandard (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨A, q, hA, hBasis⟩ := hIwahori (rootSet i ν I) (rootSet_subset i ν I)
  let L := Standard.leviScheme i ν (rootSet i ν I)
  have hL : IsConnectedReductive L := hA.standardLeviScheme_isConnectedReductive
  have := hL.isAffineHom
  have := hL.smooth
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace F L
  let : NonarchimedeanGroup (rationalPoints L) :=
    Plancherel.rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  have hcoeff := leviCompactCoefficients_of_specialVertexInputs
    hStandard hInter hRoot hInputs G hG T i hi ν hν hU I (hM I) hL E hEcusp
  have hsurj := standardFixedJacquetMap_surjective_of_generalizedJacquet i ν
    hJacquet hG hi hν hzeta hA K hK hBasis D'.representation D'.isSmooth
  have hfactor := standard_factorization_of_minimal i ν hG hi hν
    (rootSet i ν I) ⟨zeta, hzeta⟩ K0 hIwasawa
  have hcompact := standardUnipotentPoints_finite_compactOpenContainment i ν
    (rootSet i ν I) hG ⟨zeta, hzeta⟩
  have hdet := rationalLeviJacquetFixedVectorDetection_of_surjective hFinite F G hG
    T i ν I hL (hU I)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν (rootSet i ν I))
    (hM I) hcompact K K0 hK hnormal hfactor V' D' hsurj hgen' hDA' E hE hEJ hcoeff
  exact (exists_nonzero_fixed_universeLift_iff K.toSubgroup D).mp hdet

/-- The unchanged exact generation proposition follows from the four
remaining global prerequisites. This is a conditional reduction only. -/
theorem standardFixedVectorSubquotientGeneration_of_prerequisites
    (hRoot : RelativeRootSystemStatement.{u})
    (hInputs : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u})
    (hJacquet : GeneralizedJacquetLemmaStatement.{u, max (u + 1) v})
    (hFinite : CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, max (u + 1) v}) :
    StandardFixedVectorSubquotientGenerationStatement.{u, v} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro T i hi ν hν hstandard K0 _hK0 hIwasawa K hK _hKK0 hnormal hIwahori V hgen
  exact SmoothRep.fixedVectors_generate_subquotients_of_detection V K hK
    (fun D hDA hD => standardSubquotient_nonzero_fixed_of_prerequisites
      hRoot hInputs hJacquet hFinite F G hG T i hi ν hν hstandard K0 hIwasawa
      K hK hnormal hIwahori V hgen D hDA hD)

section Choice

variable (hRoot : RelativeRootSystemStatement.{u})
  (hInputs : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u})
  (hJacquet : GeneralizedJacquetLemmaStatement.{u, max (u + 1) v})
  (hFinite : CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, max (u + 1) v})
  {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)
local instance standardFixedVectorDetectionAssemblyIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance standardFixedVectorDetectionAssemblyTopologicalSpace : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
  (hν : IsGenericCocharacter i ν)
  (hstandard : ∀ J ⊆ simpleRelativeRoots i ν,
    ∃ zeta, IsStandardCocharacter i ν J zeta)
  (K0 : Subgroup (rationalPoints G))
  (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
    ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K0, g = m * n * k)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hnormal : K0 ≤ Subgroup.normalizer K.toSubgroup)
  (hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ T.toGrp),
      IsCompatibleStandardSplitComponent i ν J A q ∧
        StandardParabolicBasisMember i ν J q K.toSubgroup)
  (V : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hgen : ∀ S : Subrepresentation V.representation,
    fixedVectors V.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
  (D : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hDA : SmoothRep.IsSubquotient D V) (hD : Nontrivial D)

/-- A chosen nonzero fixed vector on the original carrier of the supplied
actual subquotient, conditional on precisely the four retained prerequisites. -/
def standardSubquotientFixedVector : fixedVectors D.representation K.toSubgroup :=
  let hex := standardSubquotient_nonzero_fixed_of_prerequisites
    hRoot hInputs hJacquet hFinite F G hG T i hi ν hν hstandard K0 hIwasawa
    K hK hnormal hIwahori V hgen D hDA hD
  ⟨hex.choose, hex.choose_spec.1⟩

/-- The chosen fixed vector is nonzero in the original representation. -/
theorem standardSubquotientFixedVector_ne_zero :
    (standardSubquotientFixedVector hRoot hInputs hJacquet hFinite G hG T i hi ν hν
      hstandard K0 hIwasawa K hK hnormal hIwahori V hgen D hDA hD : D) ≠ 0 :=
  (standardSubquotient_nonzero_fixed_of_prerequisites
    hRoot hInputs hJacquet hFinite F G hG T i hi ν hν hstandard K0 hIwasawa
    K hK hnormal hIwahori V hgen D hDA hD).choose_spec.2

end Choice

end Langlands.Jacquet
