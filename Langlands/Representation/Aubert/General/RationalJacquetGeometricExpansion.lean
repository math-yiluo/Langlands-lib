import Langlands.Representation.Aubert.General.RationalJacquetCancellation
import Langlands.Representation.Aubert.General.RationalPointSourceGeometry
import Langlands.Representation.Aubert.General.RationalGeometricK0Target

/-! # Literal rational intersection expansion from actual geometric terms -/

noncomputable section

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hStandard : StandardCocharacterStatement.{u})

local instance instRationalJacquetGeometricExpansion1 : DecidableEq (SimpleRoot i ν) := Classical.decEq _

local instance rationalJacquetGeometricExpansionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))

/-- The actual geometric expansion gives the literal intersection expansion.
The geometric decomposition and preservation witnesses may be arbitrary. -/
theorem rationalIntersectionExpansion_of_pointSource_geometricExpansion
    (hSource : PointSourceIntersectionIdentities i ν cs)
    (hGeom : GeometricIntersectionDecompositions
      (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs)
    (hTermFl : ∀ (A B : Finset (SimpleRoot i ν)) (w : Weyl i)
      (hw : IsMinimal cs A B w)
      (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w),
      GeometricTermFiniteLength.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU A B n
        (hGeom A B w hw n hn).1 (hGeom A B w hw n hn).2)
    (hExpansion : GeometricK0ExpansionStatement.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν) hU hfl hM (torusPoints i) cs hGeom hTermFl)
    (J : Finset (SimpleRoot i ν)) :
    rationalIntersectionExpansion.{u, v}
      i ν hN hZ cs hLength hSimple hG hi hν hConj
      hInter hStandard hU hM hfl hLfl J := by
  intro lift hlift I
  unfold standardAmbientJacquetK0
  rw [hExpansion J I lift hlift]
  apply Finset.sum_congr rfl
  intro w _
  exact geometricTermK0_eq_intersection_of_pointSource
    i ν cs hSource hInter hG hi hν hU hM hLfl
    hN hZ hLength hSimple hConj J I w
    ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w)
    (hGeom J I w ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w)).1
    (hGeom J I w ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w)).2
    (hTermFl J I w ((mem_minimalReps cs J I w).mp w.property) (lift w) (hlift w))

/-- The actual geometric expansion after deriving all intersection
decompositions and factor preservation from the retained point-root and
standard-Levi hypotheses. The representation equation remains unproved. -/
def rationalPointGeometricExpansion : Prop :=
  let hSource := pointSourceIntersectionIdentities
    i ν hN hZ cs hStandard hG hi hν hInter hLength hSimple
  let hGeom := geometricIntersectionDecompositions_of_pointSource
    i ν cs hSource hInter hG hi hν
  let hTermFl := fun A B w hw n hn =>
    geometricTermFiniteLength_of_pointSource.{u, v}
      i ν cs hSource hInter hG hi hν hU hM hLfl A B w hw n hn
      (hGeom A B w hw n hn).1 (hGeom A B w hw n hn).2
  GeometricK0ExpansionStatement.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν) hU hfl hM (torusPoints i) cs hGeom hTermFl

/-- The exact structural point-root hypotheses discharge the geometry
required to turn the remaining geometric expansion into the literal rows. -/
theorem rationalIntersectionExpansion_of_pointGeometricExpansion
    (hExpansion : rationalPointGeometricExpansion.{u, v}
      i ν hN hZ cs hLength hSimple hG hi hν hInter hStandard hU hM hfl hLfl)
    (J : Finset (SimpleRoot i ν)) :
    rationalIntersectionExpansion.{u, v}
      i ν hN hZ cs hLength hSimple hG hi hν hConj
      hInter hStandard hU hM hfl hLfl J := by
  let hSource := pointSourceIntersectionIdentities
    i ν hN hZ cs hStandard hG hi hν hInter hLength hSimple
  let hGeom := geometricIntersectionDecompositions_of_pointSource
    i ν cs hSource hInter hG hi hν
  let hTermFl := fun A B w hw n hn =>
    geometricTermFiniteLength_of_pointSource.{u, v}
      i ν cs hSource hInter hG hi hν hU hM hLfl A B w hw n hn
      (hGeom A B w hw n hn).1 (hGeom A B w hw n hn).2
  exact rationalIntersectionExpansion_of_pointSource_geometricExpansion.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    hInter hStandard hU hM hfl hLfl hSource hGeom hTermFl hExpansion J

omit [Fintype (SimpleRoot i ν)] in
/-- Specialize the universal rational geometric target with all its actual
geometry and factor preservation derived. Its Levi-Weyl premise stays explicit. -/
theorem rationalPointGeometricExpansion_of_rationalGeometricK0Expansion
    [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space (RationalPoint k G.X)]
    (hExpansion : RationalGeometricK0ExpansionStatement.{u, v})
    (hRoots : HasRelativeRootSystem i)
    (hP : ∀ A, IsClosed (parabolic i ν A : Set (RationalPoint k G.X)))
    (hproj : ∀ A, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν A).projection)
    (hUc : ∀ A, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν A))
    (hiFl : ∀ A, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν A) (hU A)))
    (hrFl : ∀ A, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν A) (hU A)))
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    rationalPointGeometricExpansion.{u, v}
      i ν hN hZ cs hLength hSimple hG hi hν hInter hStandard hU hM
      (standardParabolicFiniteLength.{u, v}
        i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hLfl := by
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  unfold rationalPointGeometricExpansion
  exact hExpansion k G hG T i hi ν hν hStandard hRoots
    hU hP hproj hUc hiFl hrFl hM hN hZ CM cs hLength hSimple hIdent _ _

end Langlands.Aubert.General.RationalPointFamily
