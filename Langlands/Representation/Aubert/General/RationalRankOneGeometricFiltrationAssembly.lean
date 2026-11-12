import Langlands.Representation.Aubert.General.RationalMaximalSourceGeometricFiltration
import Langlands.Representation.Aubert.General.RationalRankOneGeometricTerms
import Langlands.Representation.Aubert.General.RationalRankOneJacquetReduction
import Langlands.Representation.Filtration.LastAndSinglePrefixSequence

/-! # Rank-one Jacquet computation from ordered actual geometric filtrations -/

noncomputable section

set_option maxHeartbeats 1200000

universe u v

open Classical CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

section Local

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

local instance rankOneGeometricAssemblyPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hInter : StandardLeviIntersectionStatement.{u})
  [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)] [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
  (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
  (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ)

include hLength hSimple hJ hc in
/-- A supplied actual geometric filtration has zero ambient object at every
other proper target when the maximal source is self-associated. -/
theorem pointRankOneOtherProperJacquet_isZero_of_filtration
    (hselfJ : associatedSubset actual J = J)
    (K : Finset (SimpleRoot i ν)) (hK : K ≠ Finset.univ) (hKJ : K ≠ J)
    (D : PointGeometricObjectFiltration.{u, v}
      i ν hG hi hν hStandard hM hU actual K J σ) :
    IsZero (pointInducedJacquetObject i ν hG hi hν hStandard hU K J σ) := by
  have hz : ∀ q, Subsingleton (D.filtration.gradedRepresentation q) := by
    intro q
    have ht := pointRankOneOtherProperTerm_subsingleton
      i ν hG hi hν hStandard hN hZ hM hU hInter actual hLength hSimple
      J hJ hselfJ K hK hKJ (D.enumeration q).val
      ((mem_minimalReps actual K J _).mp (D.enumeration q).property)
      (D.lift q) (D.lift_class q) (D.source q) (D.target q) σ hc
    let _ : Subsingleton
        (((geometricTermFunctor.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
          K J (D.lift q) (D.source q) (D.target q)).obj σ).obj) := ht
    exact (Representation.equivOfIso (D.grade q)).injective.subsingleton
  apply (SmoothRep.isZero_iff_subsingleton_carrier _).mpr
  exact objectRepFiltrationSubsingleton ℂ (levi i ν K)
    (pointInducedJacquetObject i ν hG hi hν hStandard hU K J σ).obj
    (D.tailLength + 1) D.filtration hz

include hLength hSimple hJ hc in
/-- The actual self filtration with identity last gives the specified short
exact sequence for every chosen normalizing longest lift. -/
theorem pointRankOneMiddleSequence_of_filtration
    (hselfJ : associatedSubset actual J = J)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep actual J)
    (hself : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔
      (n : RationalPoint k G.X) * x * (n : RationalPoint k G.X)⁻¹ ∈ levi i ν J)
    (D : PointGeometricObjectFiltration.{u, v}
      i ν hG hi hν hStandard hM hU actual J J σ) :
    HasRankOneJacquetMiddleSequence.{u, u, max (u + 1) v}
      (h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν) (hU := hU) J σ n hself := by
  have hproper := IsMaximalStandard.ne_univ hJ
  have hlong : (longestRep actual J)⁻¹ ≠ 1 := by
    intro he
    have hp := positiveSimpleSet_longestRep actual J
    rw [inv_eq_one.mp he, hselfJ] at hp
    apply hproper
    rw [← hp]
    ext a
    simp [positiveSimpleSet, actual.length_one, actual.length_simple]
  have hmin : (longestRep actual J)⁻¹ ∈ minimalReps actual J J := by
    have hm := ((mem_simpleSurvivorPairs actual J _ _).mp
      (canonical_simpleSurvivorPairs actual J).2).2.1
    apply (mem_minimalReps actual J J _).mpr
    simpa only [hselfJ] using hm
  let d : Fin (D.tailLength + 1) :=
    D.enumeration.symm ⟨(longestRep actual J)⁻¹, hmin⟩
  have hd : (D.enumeration d).val = (longestRep actual J)⁻¹ :=
    congrArg Subtype.val (D.enumeration.apply_symm_apply _)
  have hdlast : d ≠ Fin.last D.tailLength := by
    intro he
    apply hlong
    rw [← hd, he]
    exact D.identity_last rfl
  have hdlt : d.val < D.tailLength := by
    have hlt := d.isLt
    have hne : d.val ≠ D.tailLength := by
      intro he
      exact hdlast (Fin.ext he)
    omega
  let q₀ : Fin D.tailLength := ⟨d.val, hdlt⟩
  have hq₀ : q₀.castSucc = d := Fin.ext rfl
  have hq₀class : (D.enumeration q₀.castSucc).val = (longestRep actual J)⁻¹ := by
    rw [hq₀]
    exact hd
  let τ := (conjugationFunctor (n : RationalPoint k G.X)⁻¹
    (fun x => by simpa using hself x)).obj σ
  have eτ : D.filtration.gradedRepresentation q₀.castSucc ≅ τ.obj :=
    D.grade q₀.castSucc ≪≫ SmoothRep.toRep.mapIso
      (pointRankOneInverseLongestTermIso i ν hZ hM hU actual J n hn hself
        (D.lift q₀.castSucc) ((D.lift_class _).trans hq₀class)
        (D.source _) (D.target _) σ)
  have eσ : D.filtration.gradedRepresentation (Fin.last D.tailLength) ≅ σ.obj :=
    D.grade (Fin.last D.tailLength) ≪≫ SmoothRep.toRep.mapIso
      (pointGeometricTermIdentityClassIso i ν hZ hM hU J
        (D.lift (Fin.last D.tailLength))
        ((D.lift_class _).trans (D.identity_last rfl))
        (D.source _) (D.target _) σ)
  apply smooth_shortExact_of_last_and_single_prefix D.filtration q₀ eτ eσ
  intro q hq
  have hw1 : (D.enumeration q.castSucc).val ≠ 1 := by
    intro he
    have hidx := D.enumeration.injective
      (Subtype.ext (he.trans (D.identity_last rfl).symm))
    have hv := congrArg Fin.val hidx
    have hlt := q.isLt
    change q.val = D.tailLength at hv
    omega
  have hwlong : (D.enumeration q.castSucc).val ≠ (longestRep actual J)⁻¹ := by
    intro he
    have hidx := D.enumeration.injective (Subtype.ext (he.trans hq₀class.symm))
    exact hq (Fin.ext (congrArg (fun a : Fin (D.tailLength + 1) => a.val) hidx))
  have ht := pointRankOneSelfTerm_subsingleton_of_other_class
    i ν hG hi hν hStandard hN hZ hM hU hInter actual hLength hSimple
    J hJ (D.enumeration q.castSucc).val
    ((mem_minimalReps actual J J _).mp (D.enumeration q.castSucc).property)
    hw1 hwlong (D.lift q.castSucc) (D.lift_class _) (D.source _) (D.target _) σ hc
  let _ : Subsingleton
      (((geometricTermFunctor.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
        J J (D.lift q.castSucc) (D.source _) (D.target _)).obj σ).obj) := ht
  exact (Representation.equivOfIso (D.grade q.castSucc)).injective.subsingleton

end Local

set_option linter.defProp false in
/-- Ordered actual geometric filtrations for maximal sources suffice for the
whole rational rank-one geometric Jacquet statement. The filtration premise
remains unproved. -/
def rationalRankOneGeometricJacquetOfMaximalSourceFiltration :
    RationalMaximalSourceGeometricFiltrationStatement.{u, v} →
      RationalRankOneGeometricJacquetStatement.{u, v} := by
  intro hfil k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ hc n hn hself
  have hselfJ := pointAssociatedSubset_eq_of_normalizing_longestLift
    i ν hG hi hν hStandard hN hZ actual hLength hSimple hMin hAssoc hIdent J n hn hself
  have hfilJ := hfil k G hG T i hi ν hν hStandard hInter hRoots hU hM
    hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ
  obtain ⟨D⟩ := hfilJ J (IsMaximalStandard.ne_univ hJ)
  refine ⟨pointRankOneMiddleSequence_of_filtration
    i ν hG hi hν hStandard hN hZ hM hU hInter actual hLength hSimple
    J hJ σ hc hselfJ n hn hself D, ?_⟩
  intro K hK hKJ
  obtain ⟨D⟩ := hfilJ K hK
  exact pointRankOneOtherProperJacquet_isZero_of_filtration
    i ν hG hi hν hStandard hN hZ hM hU hInter actual hLength hSimple
    J hJ σ hc hselfJ K hK hKJ D

end Langlands.Aubert.General.RationalPointFamily
