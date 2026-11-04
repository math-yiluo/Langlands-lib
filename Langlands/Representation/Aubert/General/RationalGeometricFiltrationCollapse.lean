import Langlands.Representation.Aubert.General.RationalGeometricLiftComparison
import Langlands.Representation.Filtration.SingleSurvivingGrade
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Conditional collapse of actual rational geometric filtrations -/

noncomputable section

universe uR uG uH uV u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Smooth

variable {R : Type uR} [CommRing R] {H : Type uG} [Group H] [TopologicalSpace H]
  {A : SmoothRep.{uR, uG, uV} R H} {N : ℕ}

/-- Identify the whole smooth object from its actual finite filtration,
specified smooth graded pieces, and a single potentially nonzero occurrence. -/
def smoothSingleSurvivingPieceIso
    (s : ObjectRepFiltration A.obj N)
    (pieces : Fin N → SmoothRep.{uR, uG, uV} R H)
    (grades : ∀ q, s.gradedRepresentation q ≅ (pieces q).obj)
    (q₀ : Fin N) (hz : ∀ q, q ≠ q₀ → Subsingleton (pieces q)) :
    A ≅ pieces q₀ := by
  have hs : ∀ q, q ≠ q₀ → Subsingleton (s.gradedRepresentation q) := by
    intro q hq
    let _ := hz q hq
    exact (Representation.equivOfIso (grades q)).injective.subsingleton
  exact SmoothRep.mkIso
    (Representation.equivOfIso (s.singleSurvivingGradeIso q₀ hs ≪≫ grades q₀))

end Smooth

section Irreducible

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {K : Type uH} [Group K] [TopologicalSpace K]

/-- An actual isomorphism to an equivalence pullback transports irreducibility
from the original representation. -/
theorem smooth_isIrreducible_of_iso_pullback
    (e : H ≃ₜ* K) (A : SmoothRep.{0, uH, uV} ℂ K)
    (B : SmoothRep.{0, uG, uV} ℂ H)
    (h : B ≅ (SmoothRep.pullbackFunctor e).obj A)
    (hA : A.IsIrreducible) : B.IsIrreducible :=
  SmoothRep.isIrreducible_of_iso h.symm
    ((Langlands.isIrreducible_comp_continuousMulEquiv_iff A.representation e).mpr hA)

end Irreducible

namespace RationalPointFamily

open SmoothRep GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hStandard : StandardCocharacterStatement.{u})

local instance rationalGeometricFiltrationCollapsePointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- The original actual normalized Jacquet module of the original actual
normalized induction, retaining the source and target Levi labels. -/
def pointInducedJacquetObject (I J : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I) :=
  (jacquetFunctor.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) (hU I)).obj
    ((normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J) (hU J)).obj σ)

variable (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hInter : StandardLeviIntersectionStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)
  (hMin : minimalityLengthCriterion actual)

section Self

variable (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
  (hne : J ≠ associatedSubset actual J)
  (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
  (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ)
  {N : ℕ} (w : Fin N → Weyl i)
  (hw : ∀ q, IsMinimal actual J J (w q)) (winj : Function.Injective w)
  (n : Fin N → Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : ∀ q, QuotientGroup.mk (n q) = w q)
  (hs : ∀ q, GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
    J J (n q : RationalPoint k G.X))
  (ht : ∀ q, GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
    J J (n q : RationalPoint k G.X))
  (s : ObjectRepFiltration
    (pointInducedJacquetObject i ν hG hi hν hStandard hU J J σ).obj N)
  (grades : ∀ q, s.gradedRepresentation q ≅
    ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J (n q)
      (hs q) (ht q)).obj σ).obj)
  (q₀ : Fin N) (hq₀ : w q₀ = 1)

set_option maxHeartbeats 1000000 in
/-- A supplied actual geometric filtration collapses to the original cuspidal
object for a maximal non-self-associated source Levi. -/
def pointSelfJacquetIsoOfGeometricFiltration :
    pointInducedJacquetObject i ν hG hi hν hStandard hU J J σ ≅ σ := by
  let pieces := fun q : Fin N =>
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J J (n q)
      (hs q) (ht q)).obj σ
  have hz : ∀ q, q ≠ q₀ → Subsingleton (pieces q) := by
    intro q hq
    have hwne : w q ≠ 1 := by
      intro heq
      exact hq (winj (heq.trans hq₀.symm))
    exact pointGeometricSelfTerm_subsingleton_of_ne_one
      (i := i) (ν := ν) (hG := hG) (hi := hi) (hν := hν)
      (hStandard := hStandard) (hN := hN) (hZ := hZ) (hM := hM) (hU := hU)
      (actual := actual) (hLength := hLength) (hSimple := hSimple)
      (hMin := hMin) (hInter := hInter)
      J hJ hne (w q) (hw q) hwne (n q) (hn q) (hs q) (ht q) σ hc
  exact smoothSingleSurvivingPieceIso s pieces grades q₀ hz ≪≫
    pointGeometricTermIdentityClassIso i ν hZ hM hU J (n q₀)
      ((hn q₀).trans hq₀) (hs q₀) (ht q₀) σ

set_option maxHeartbeats 1000000 in
include hLength hSimple hMin hJ hne hc hw winj hn grades hq₀ in
/-- Under the displayed actual-filtration inputs, the self Jacquet module of
the induction is irreducible whenever the inducing object is irreducible. -/
theorem pointSelfJacquet_isIrreducible_of_geometricFiltration
    (hσ : σ.IsIrreducible) :
    (pointInducedJacquetObject i ν hG hi hν hStandard hU J J σ).IsIrreducible :=
  SmoothRep.isIrreducible_of_iso
    (pointSelfJacquetIsoOfGeometricFiltration
      (i := i) (ν := ν) (hG := hG) (hi := hi) (hν := hν)
      (hStandard := hStandard) (hU := hU) (hM := hM) (hInter := hInter)
      (hN := hN) (hZ := hZ) (actual := actual) (hLength := hLength)
      (hSimple := hSimple) (hMin := hMin) (J := J) (hJ := hJ) (hne := hne)
      (σ := σ) (hc := hc) (w := w) (hw := hw) (winj := winj) (n := n)
      (hn := hn) (hs := hs) (ht := ht) (s := s) (grades := grades)
      (q₀ := q₀) (hq₀ := hq₀)).symm hσ

end Self

section Associated

variable (hAssoc : associatedSubsetLaws actual)
  (J : Finset (SimpleRoot i ν)) (hJ : IsMaximalStandard J)
  (hne : J ≠ associatedSubset actual J)
  (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J))
  (hc : IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) J (hM J)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) hU σ)
  (n₀ : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn₀ : QuotientGroup.mk n₀ = longestRep actual J)
  {N : ℕ} (w : Fin N → Weyl i)
  (hw : ∀ q, IsMinimal actual (associatedSubset actual J) J (w q))
  (winj : Function.Injective w)
  (n : Fin N → Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : ∀ q, QuotientGroup.mk (n q) = w q)
  (hs : ∀ q, GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
    (associatedSubset actual J) J (n q : RationalPoint k G.X))
  (ht : ∀ q, GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν)
    (associatedSubset actual J) J (n q : RationalPoint k G.X))
  (s : ObjectRepFiltration
    (pointInducedJacquetObject i ν hG hi hν hStandard hU
      (associatedSubset actual J) J σ).obj N)
  (grades : ∀ q, s.gradedRepresentation q ≅
    ((geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
      (associatedSubset actual J) J (n q) (hs q) (ht q)).obj σ).obj)
  (q₀ : Fin N) (hq₀ : w q₀ = (longestRep actual J)⁻¹)

set_option maxHeartbeats 1000000 in
/-- A supplied actual geometric filtration toward the associated Levi collapses
to inverse associated-Levi transport for any fixed chosen longest lift. -/
def pointAssociatedJacquetIsoOfGeometricFiltration :
    pointInducedJacquetObject i ν hG hi hν hStandard hU
        (associatedSubset actual J) J σ ≅
      (SmoothRep.pullbackFunctor (associatedLeviConjugationEquiv i ν hG hi hν
        (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
        hN hZ actual hLength hSimple hMin hAssoc J n₀ hn₀).symm).obj σ := by
  let pieces := fun q : Fin N =>
    (geometricTermFunctor.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU
      (associatedSubset actual J) J (n q) (hs q) (ht q)).obj σ
  have hz : ∀ q, q ≠ q₀ → Subsingleton (pieces q) := by
    intro q hq
    have hwne : w q ≠ (longestRep actual J)⁻¹ := by
      intro heq
      exact hq (winj (heq.trans hq₀.symm))
    exact pointGeometricAssociatedTerm_subsingleton_of_ne_inv_longest
      (i := i) (ν := ν) (hG := hG) (hi := hi) (hν := hν)
      (hStandard := hStandard) (hN := hN) (hZ := hZ) (hM := hM) (hU := hU)
      (actual := actual) (hLength := hLength) (hSimple := hSimple)
      (hMin := hMin) (hInter := hInter)
      J hJ hne (w q) (hw q) hwne (n q) (hn q) (hs q) (ht q) σ hc
  exact smoothSingleSurvivingPieceIso s pieces grades q₀ hz ≪≫
    pointGeometricTermInverseLongestClassIso i ν hZ hM hU hG hi hν hStandard hN
      actual hLength hSimple hMin hAssoc J n₀ hn₀ (n q₀)
      ((hn q₀).trans hq₀) (hs q₀) (ht q₀) σ

set_option maxHeartbeats 1000000 in
include hLength hSimple hMin hAssoc hJ hne hc hn₀ hw winj hn grades hq₀ in
/-- Under the displayed actual-filtration inputs, the associated Jacquet
module of the induction is irreducible for irreducible inducing data. -/
theorem pointAssociatedJacquet_isIrreducible_of_geometricFiltration
    (hσ : σ.IsIrreducible) :
    (pointInducedJacquetObject i ν hG hi hν hStandard hU
      (associatedSubset actual J) J σ).IsIrreducible := by
  exact smooth_isIrreducible_of_iso_pullback
    (associatedLeviConjugationEquiv i ν hG hi hν
      (standardLeviConjugationStatement_of_standardCocharacterStatement hStandard)
      hN hZ actual hLength hSimple hMin hAssoc J n₀ hn₀).symm σ
    (pointInducedJacquetObject i ν hG hi hν hStandard hU
      (associatedSubset actual J) J σ)
    (pointAssociatedJacquetIsoOfGeometricFiltration
      (i := i) (ν := ν) (hG := hG) (hi := hi) (hν := hν)
      (hStandard := hStandard) (hU := hU) (hM := hM) (hInter := hInter)
      (hN := hN) (hZ := hZ) (actual := actual) (hLength := hLength)
      (hSimple := hSimple) (hMin := hMin) (hAssoc := hAssoc)
      (J := J) (hJ := hJ) (hne := hne) (σ := σ) (hc := hc)
      (n₀ := n₀) (hn₀ := hn₀) (w := w) (hw := hw) (winj := winj) (n := n)
      (hn := hn) (hs := hs) (ht := ht) (s := s) (grades := grades)
      (q₀ := q₀) (hq₀ := hq₀)) hσ

end Associated

end RationalPointFamily

end Langlands.Aubert.General
