import Langlands.Representation.Aubert.General.RationalGeometricOrbitTerm
import Langlands.Representation.Aubert.General.RationalGeometricOrbitOrdering
import Langlands.Representation.Filtration.GrothendieckProof

/-!
# The rational geometric-lemma K0 expansion from parabolic points and epsilon balance

The actual support filtration of `r_I ∘ i_J`, ordered by the lifts of the
minimal representatives, has the published normalized geometric terms as its
graded pieces once the two original epsilon corrections cancel. Exact K0
additivity then gives the expansion.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

/-- A filtration with the given graded pieces glues them, in the given order. -/
theorem isGluedFrom_of_hasGradedPieces {R : Type*} [CommRing R] {H : Type*} [Monoid H]
    {C : Type*} [Category C] {F : C ⥤ Rep R H} {n : ℕ} {pieces : Fin n → C ⥤ Rep R H}
    (s : RepFunctorFiltration F n) (h : s.HasGradedPieces pieces) : IsGluedFrom F pieces :=
  ⟨Equiv.refl _, s, h⟩

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rationalGeometricK0ReductionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLevi : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
  (hGeom : GeometricIntersectionDecompositions
    (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs)
  (hTermFl : ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i)
    (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = w),
    GeometricTermFiniteLength.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
      (n : RationalPoint k G.X)
      (hGeom I J w hw n hn).1 (hGeom I J w hw n hn).2)

include hN hZ hLevi in
/-- The rational geometric-lemma K0 expansion, from the standard-parabolic
points statement and cancellation of the two original epsilon corrections. -/
theorem geometricK0Expansion_of_points_of_balance
    (hPoints : StandardParabolicPointsStatement.{u})
    (hε : ∀ (I J : Finset (SimpleRoot i ν))
      (n : Group.RelativeWeyl.normalizer (torusPoints i)),
      geometricEpsilonOne i ν I J
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
          n (hU J) (hP I) *
        geometricEpsilonTwo i ν I J
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
          n (hU I) (hP J) = 1) :
    GeometricK0ExpansionStatement.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
      (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
      hM (torusPoints i) cs hGeom hTermFl := by
  intro I J lift hlift
  let dec := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  let fl := standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
  have := reductiveRationalPoint_secondCountable k G hG
  obtain ⟨m, e, t, ht⟩ :=
    minimalOrbitOrdering i ν hPoints hG hi hν hN hZ cs hLevi I J (hP J) (hP I) lift hlift
  let hw (q : Fin m) : IsMinimal cs I J (e q).val :=
    (mem_minimalReps cs I J (e q).val).mp (e q).property
  let Pc (q : Fin m) := geometricTermFunctor.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
    ((lift (e q).val : Group.RelativeWeyl.normalizer (torusPoints i)) : RationalPoint k G.X)
    (hGeom I J (e q).val (hw q) (lift (e q).val) (hlift _)).1
    (hGeom I J (e q).val (hw q) (lift (e q).val) (hlift _)).2
  have hgr : ∀ q, Nonempty ((jacquetSupportFiltration.{u, max (u + 1) v}
      (dec J) (hU J) (dec I) (hU I) t).graded q ≅ Pc q ⋙ SmoothRep.toRep) := fun q =>
    ⟨jacquetSupportGeometricTermIso.{u, max (u + 1) v} i ν I J (lift (e q).val)
      hStandard hG hi hν hN (dec I) (dec J) hM hU (hP I) (hP J) (hproj I) (hproj J)
      (hUc I) (hUc J)
      (hGeom I J (e q).val (hw q) (lift (e q).val) (hlift _)).1
      (hGeom I J (e q).val (hw q) (lift (e q).val) (hlift _)).2
      (hε I J (lift (e q).val)) t q (ht q)⟩
  have hg0 : IsGluedFrom
      (normalizedInductionFunctor.{u, max (u + 1) v} (dec J) (hU J) ⋙
        jacquetFunctor.{u, max (u + 1) v} (dec I) (hU I) ⋙ SmoothRep.toRep)
      (fun q => Pc q ⋙ SmoothRep.toRep) :=
    isGluedFrom_of_hasGradedPieces (pieces := fun q => Pc q ⋙ SmoothRep.toRep)
      (jacquetSupportFiltration.{u, max (u + 1) v} (dec J) (hU J) (dec I) (hU I) t) hgr
  have hg : IsGluedFrom
      ((normalizedInductionFunctor.{u, max (u + 1) v} (dec J) (hU J) ⋙
        jacquetFunctor.{u, max (u + 1) v} (dec I) (hU I)) ⋙ SmoothRep.toRep)
      (fun q => Pc q ⋙ SmoothRep.toRep) := by
    rw [Functor.assoc]
    exact hg0
  apply FiniteLengthGrothendieckGroup.hom_ext_object
  intro X
  have hInd : ((normalizedInductionFunctor.{u, max (u + 1) v} (dec J) (hU J)).obj
      X.val).HasFiniteLength := (fl J).1 X.val X.property
  have hF : ((normalizedInductionFunctor.{u, max (u + 1) v} (dec J) (hU J) ⋙
      jacquetFunctor.{u, max (u + 1) v} (dec I) (hU I)).obj X.val).HasFiniteLength :=
    (fl I).2.2.1 _ hInd
  obtain ⟨hPc, hclass⟩ := SmoothRep.filtrationGrothendieckStatement ℂ (levi i ν I)
    (SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) _ m Pc hg X.val hF
  have hX : FiniteLengthGrothendieckGroup.ofObject X =
      FiniteLengthGrothendieckGroup.ofRepresentation X.val X.property := rfl
  rw [hX, LinearMap.comp_apply, inductionK0_ofRepresentation, jacquetK0_ofRepresentation]
  refine hclass.trans ?_
  rw [LinearMap.sum_apply]
  refine Fintype.sum_equiv e _ _ (fun q => ?_)
  exact (geometricTermK0_ofRepresentation _ _ _ _ _ _ _ _ _ _ _ X.val X.property).symm

set_option linter.defProp false in
include hN hZ hLevi in
/-- The conditional expansion `geometricK0Expansion_of_points_of_balance`, as a
declaration whose type is the implication from the parabolic points statement
and the epsilon cancellation to the target's expansion. -/
def geometricK0ExpansionOfPointsOfBalance :
    StandardParabolicPointsStatement.{u} →
    (∀ (I J : Finset (SimpleRoot i ν))
      (n : Group.RelativeWeyl.normalizer (torusPoints i)),
      geometricEpsilonOne i ν I J
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
          n (hU J) (hP I) *
        geometricEpsilonTwo i ν I J
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
          n (hU I) (hP J) = 1) →
    GeometricK0ExpansionStatement.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
      (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
      hM (torusPoints i) cs hGeom hTermFl :=
  fun hPoints hε => geometricK0Expansion_of_points_of_balance i ν hStandard hG hi hν hU hP hproj
    hUc hiFl hrFl hM hN hZ cs hLevi hGeom hTermFl hPoints hε

end Langlands.Aubert.General.RationalPointFamily
