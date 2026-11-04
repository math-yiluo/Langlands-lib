import Langlands.Representation.Smooth.Admissibility.RationalHoweJointAssemblyStatement
import Langlands.Representation.Smooth.Admissibility.RationalHoweAssemblyProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Rational Howe assembly from the joint basis's reductive Levi witnesses -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

open GroupScheme

/-- A compatible component supplies a reductive representative of the standard
Levi subgroup functor, hence also reductivity of its canonical representative. -/
theorem IsCompatibleStandardSplitComponent.standardLeviScheme_isConnectedReductive
    {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
    {J : Set (characterLattice S)}
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν J A q) :
    IsConnectedReductive (Standard.leviScheme i ν J) := by
  obtain ⟨M, j, a, hrep, -, hM, -, -⟩ := hA.2
  exact (Standard.isRepresentedBy_leviHom i ν J).isConnectedReductive hrep hM

end Langlands.BruhatTits.SpecialCompact

namespace Langlands.SmoothRep

open GroupScheme Aubert.General Aubert.General.RationalPointFamily
open BruhatTits.SpecialCompact

set_option maxHeartbeats 1600000 in
/-- The six retained prerequisites imply precisely the rational Howe
finite-length implication, with independent field and carrier universes. -/
theorem rationalHoweJointAssembly : RationalHoweJointAssemblyStatement.{u, v} := by
  intro hStandard hInter hRoot hJoint hCompact hFinite F _ _ _ _ G hG
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
  obtain ⟨hInherited, component, q, hcomponent, hmembers⟩ :=
    hBJ (rootSet i ν I) (rootSet_subset i ν I)
  let L := Standard.leviScheme i ν (rootSet i ν I)
  have hL : IsConnectedReductive L :=
    hcomponent.standardLeviScheme_isConnectedReductive
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
