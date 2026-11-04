import Langlands.Representation.Smooth.Admissibility.RationalHoweAssemblyStatement
import Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Smooth.FixedVectors.RationalLeviJacquetDetectionProof
import Langlands.Representation.Smooth.FixedVectors.DetectionConsequencesProof
import Langlands.Representation.Smooth.FixedVectors.RefinedGeneratorsProof
import Langlands.Representation.Category.UniverseLiftFinitenessProof
import Langlands.BruhatTits.SpecialCompact.JacquetContractionAssembly
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # Conditional assembly of Howe's rational-point implication -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact

/-- The joint geometric witness supplies all compactness inputs at one local
special compact subgroup of the group under consideration. -/
theorem compactCoefficients_of_jointBasis
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hCompact : RationalCuspidalCompactRestrictionStatement.{u, v})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
    (hν : IsGenericCocharacter i ν)
    (hStandard : StandardCocharacterStatement.{u}) (hRoots : HasRelativeRootSystem i) :
    have := hG.isAffineHom
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [T2Space (rationalPoints G)]
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G))),
      let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ E : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
          hU E →
        HasCompactSmoothDualCoefficients
          (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) E).representation := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ _ _ _ hU
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ E hE
  obtain ⟨D, x, Z, j, s, -, hrep, hcomp, h, hspecial, hprops, -, -, hcartan,
    -, -, hbasis⟩ := hJoint F G hG T i hi ν hν
  have hcover := rationalPositiveCartanCover F G T i ν D x Z j s h hrep hcomp hcartan
  exact hCompact F G hG T i hi ν hν hStandard hRoots hU D x hspecial
    hprops hbasis hcover E hE

set_option maxHeartbeats 800000 in
/-- Literal inside-Levi cuspidality yields compact coefficients on the
intrinsic common norm kernel of the actual standard Levi scheme. -/
theorem leviCompactCoefficients_of_jointBasis
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hRoot : RelativeRootSystemStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hCompact : RationalCuspidalCompactRestrictionStatement.{u, v})
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
  exact compactCoefficients_of_jointBasis hJoint hCompact L hL T iL hiL ν hνL
    hStandard hRootsL hUL (SmoothRep.pullback (leviRationalPointHomeomorph i ν I) E) hEcusp

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.SmoothRep

open GroupScheme Aubert.General Aubert.General.RationalPointFamily
open BruhatTits.SpecialCompact

set_option maxHeartbeats 1600000 in
/-- The seven retained prerequisites imply precisely the rational Howe
finite-length implication, with independent field and carrier universes. -/
theorem rationalHoweAssembly : RationalHoweAssemblyStatement.{u, v} := by
  intro hStandard hInter hRoot hLevi hJoint hCompact hFinite F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  intro A hfg hadm
  let A' := universeLift.{u + 1} A
  have hfg' : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) A'.representation.asModule :=
    (moduleFinite_universeLift_iff A).mpr hfg
  have hadm' : A'.IsAdmissible := (isAdmissible_universeLift_iff A).mpr hadm
  apply (hasFiniteLength_universeLift_iff A).mp
  change A'.HasFiniteLength
  classical
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  have hRoots := hRoot F G hG T i hi
  obtain ⟨Dgeom, xgeom, Z, j, s, -, -, -, hchar, -, -, -, hproducts, -, -, -, hbasis⟩ :=
    hJoint F G hG T i hi ν hν
  let K0 := Dgeom.specialCompactSubgroup xgeom
  obtain ⟨B, hB, hBJ⟩ := hbasis
  obtain ⟨n, generators, Ksub, hKB, -, -, -, hgenerate⟩ :=
    commonBasisFixedGenerators ℂ (rationalPoints G) A' A'.representation
      A'.isSmooth hfg' B hB.2 Set.univ (Filter.univ_mem)
  obtain ⟨hKK0, hnormal, hopen, hKcompact⟩ := hB.1 Ksub hKB
  let K : OpenSubgroup (rationalPoints G) := ⟨Ksub, hopen⟩
  have hKnormal : K0 ≤ Subgroup.normalizer K.toSubgroup :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKK0).mp hnormal
  let : FiniteDimensional ℂ (fixedVectors A'.representation K.toSubgroup) := hadm'.2 K
  apply (compactOpenDetectionConsequences (rationalPoints G) A' K hKcompact ?_).2.2.2
  intro D hD hDA
  let : Representation.IsIrreducible D.representation := hD
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) D.representation.asModule
  let hU := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  let hM := isClosed_levi_of_isNonarchimedeanLocalField i ν
  obtain ⟨I, -, E, hE, hEcusp, hEJ⟩ :=
    exists_irreducible_cuspidal_jacquet_subquotient
      i ν hStandard hInter hRoots hG hi hν hU hM D
  let L := Standard.leviScheme i ν (rootSet i ν I)
  have hL : IsConnectedReductive L :=
    (hLevi F G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1
  have := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have := hL.smooth
  let : TopologicalSpace (rationalPoints L) := rationalPointTopology F L.X
  let : LocallyCompactSpace (rationalPoints L) := rationalPoint_locallyCompactSpace F L
  let : NonarchimedeanGroup (rationalPoints L) :=
    Plancherel.rationalPoints_nonarchimedeanGroup L
  let : T2Space (rationalPoints L) := rationalPoint_t2Space F L
  have hcoeff := leviCompactCoefficients_of_jointBasis
    hStandard hInter hRoot hJoint hCompact G hG T i hi ν hν hU I (hM I) hL E hEcusp
  obtain ⟨hInherited, component, q, hcomponent, hmembers⟩ :=
    hBJ (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨⟨ζ, hζ⟩, hcomparison⟩ :=
    hStandard F G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  let g := hcomponent.strictElement i ν hi hζ
  obtain ⟨hgM, hgCA, hgplus, hgstrict⟩ := hcomponent.strictElement_spec i ν hi hζ
  have hcontraction := isIwahoriContraction_of_contractionAndCofinality
    hopen (hmembers Ksub hKB).1 (hmembers Ksub hKB).2 hgM hgCA hgplus hgstrict
  have hdecomposition : ∀ z : rationalPoints G,
      ∃ m ∈ levi i ν I, ∃ n ∈ unipotent i ν I, ∃ k ∈ K0, z = m * n * k := by
    intro z
    have hz : z ∈ (parabolic i ν I : Set (rationalPoints G)) *
        (K0 : Set (rationalPoints G)) := by
      rw [← (hproducts.2.2.1 (rootSet i ν I) (rootSet_subset i ν I)).1]
      trivial
    obtain ⟨p, hp, k, hk, hpk⟩ := Set.mem_mul.mp hz
    obtain ⟨m, hm, n, hn, hmn⟩ := exists_mul_of_mem_parabolic hG hi hν hStandard I hp
    exact ⟨m, hm, n, hn, k, hk, by rw [← hpk, hmn]⟩
  have hcompactN : ∀ t : Finset (unipotent i ν I),
      ∃ J : OpenSubgroup (unipotent i ν I),
        IsCompact (J : Set (unipotent i ν I)) ∧ ∀ n ∈ t, n ∈ J := by
    have hNeq := (hcomparison ζ hζ).2.2
    change ∀ t : Finset ((standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _))),
      ∃ J : OpenSubgroup ((standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _))),
        IsCompact (J : Set ((standardUnipotent i ν (rootSet i ν I)).carrier
          (Over.mk (𝟙 _)))) ∧ ∀ n ∈ t, n ∈ J
    rw [hNeq]
    intro t
    obtain ⟨J, hJ, htJ⟩ := BruhatTits.dynamicUnipotentCompactOpenContainment
      F G hG (CommGroupScheme.groupHom ζ ≫ i) (t : Set _) t.finite_toSet.isCompact
    exact ⟨J, hJ, fun n hn => htJ hn⟩
  exact rationalLeviJacquetFixedVectorDetection hFinite F G hG T i ν I hL
    (standardOppositeUnipotentPoints i ν (rootSet i ν I))
    (hU I)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).levi_le_normalizer
    (hM I) hcompactN K K0 hKcompact hKnormal hdecomposition g hcontraction A' D
    (inferInstance : FiniteDimensional ℂ (fixedVectors A'.representation K.toSubgroup))
    (hgenerate K.toSubgroup le_rfl) hDA E hE hEJ hcoeff

end Langlands.SmoothRep
