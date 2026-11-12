import Langlands.Representation.Aubert.General.RationalMaximalSourceGeometricFiltration
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionGeometry
import Langlands.Representation.Aubert.General.RationalGeometricOrbitOrdering
import Langlands.Representation.Aubert.General.RationalGeometricOrbitTerm
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Geometric.ClosedOrbitLast
import Langlands.GroupScheme.Rational.StandardParabolicPointsProof

/-! # Actual ordered object filtrations from cancellation of the Haar corrections -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

local instance geometricObjectConstructionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  [Fintype (Weyl i)]
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) actual)

/-- Actual minimal-class orbit ordering, with identity last for a self
composite. Finiteness and the endpoint refinement are proved here. -/
def pointMinimalOrbitOrderingIdentityLast (I J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w) :
    Σ N : ℕ,
      Σ e : Fin (N + 1) ≃ {w : Weyl i // w ∈ minimalReps actual I J},
        {t : Geometric.OrderedDoubleCosets (parabolic i ν J) (parabolic i ν I) (N + 1) //
          (∀ q, t.representative q = (lift (e q).val : RationalPoint k G.X)) ∧
          (I = J → (e (Fin.last N)).val = 1)} := by
  have := reductiveRationalPoint_secondCountable k G hG
  let hP := isClosed_standard_parabolic i ν hStandard hG hi hν
  obtain ⟨m, e, t, ht⟩ := minimalOrbitOrdering i ν standardParabolicPointsStatement_proof
    hG hi hν hN hZ actual hIdent I J (hP J) (hP I) lift hlift
  have hm : m ≠ 0 := by
    intro he
    have hlt := (e.symm ⟨1, (mem_minimalReps actual I J 1).mpr (isMinimal_one actual I J)⟩).isLt
    omega
  have hm' : m = (m - 1) + 1 := by omega
  generalize m - 1 = N at hm'
  subst m
  by_cases hIJ : I = J
  · subst I
    let p := e.symm ⟨1, (mem_minimalReps actual J J 1).mpr (isMinimal_one actual J J)⟩
    have hep : (e p).val = 1 := congrArg Subtype.val (e.apply_symm_apply _)
    have hrep : t.representative p ∈ parabolic i ν J := by
      rw [ht]
      apply (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν J).levi_le
      exact normalizerLift_mem_levi_of_mk_eq_one i ν hZ J (lift (e p).val)
        ((hlift _).trans hep)
    let : T2Space (Induction.LeftQuotient (parabolic i ν J)) :=
      QuotientIntegration.leftQuotient_t2Space _ (hP J)
    have hclosed : IsClosed (Geometric.cosetOrbit
        (parabolic i ν J) (parabolic i ν J) (t.representative p)) := by
      rw [Geometric.cosetOrbit_self_eq_singleton _ _ hrep]
      exact isClosed_singleton
    refine ⟨N, (Geometric.moveLastPermutation p).trans e, t.closedOrbitLast p hclosed, ?_, ?_⟩
    · intro q
      exact ht (Geometric.moveLastPermutation p q)
    · intro _
      simpa using hep
  · exact ⟨N, e, t, ht, fun h => (hIJ h).elim⟩

variable (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hInter : StandardLeviIntersectionStatement.{u})
  [Fintype (SimpleRoot i ν)]
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ actual)

/-- The actual object filtration, including its identity-last condition,
provided the original two Haar corrections cancel at every minimal lift.
No finiteness condition on the input representation is assumed. -/
def pointGeometricObjectFiltrationOfEpsilonBalance
    (I J : Finset (SimpleRoot i ν))
    (hε : ∀ (w : Weyl i), IsMinimal actual I J w →
      ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i)), QuotientGroup.mk n = w →
        geometricEpsilonOne i ν I J
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν I)
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν J)
            n (hU J) (isClosed_standard_parabolic i ν hStandard hG hi hν I) *
          geometricEpsilonTwo i ν I J
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν I)
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν J)
            n (hU I) (isClosed_standard_parabolic i ν hStandard hG hi hν J) = 1)
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) :
    PointGeometricObjectFiltration.{u, v} i ν hG hi hν hStandard hM hU actual I J σ := by
  let dec := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  let hP := isClosed_standard_parabolic i ν hStandard hG hi hν
  let hproj := continuous_standard_projection i ν hStandard hG hi hν
  let hUc := standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
    i ν hStandard hG hi hν
  let hSource := pointSourceIntersectionIdentities
    i ν hN hZ actual hStandard hG hi hν hInter hLength hSimple
  let hGeom := geometricIntersectionDecompositions_of_pointSource
    i ν actual hSource hInter hG hi hν
  let lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i) :=
    fun w => Classical.choose (QuotientGroup.mk_surjective w)
  have hlift : ∀ w, QuotientGroup.mk (lift w) = w :=
    fun w => Classical.choose_spec (QuotientGroup.mk_surjective w)
  obtain ⟨N, e, t, ht, hlast⟩ :=
    pointMinimalOrbitOrderingIdentityLast i ν hG hi hν hStandard hN hZ actual hIdent I J lift hlift
  let hw (q : Fin (N + 1)) : IsMinimal actual I J (e q).val :=
    (mem_minimalReps actual I J _).mp (e q).property
  let hs (q : Fin (N + 1)) := (hGeom I J (e q).val (hw q) (lift (e q).val) (hlift _)).1
  let htgt (q : Fin (N + 1)) := (hGeom I J (e q).val (hw q) (lift (e q).val) (hlift _)).2
  let s := jacquetSupportFiltration.{u, max (u + 1) v}
    (dec J) (hU J) (dec I) (hU I) t
  refine
    { tailLength := N
      enumeration := e
      lift := fun q => lift (e q).val
      lift_class := fun q => hlift _
      source := hs
      target := htgt
      filtration := s.atObject σ
      grade := ?_
      identity_last := hlast }
  intro q
  exact (jacquetSupportGeometricTermIso.{u, max (u + 1) v}
    i ν I J (lift (e q).val) hStandard hG hi hν hN (dec I) (dec J) hM hU
    (hP I) (hP J) (hproj I) (hproj J) (hUc I) (hUc J) (hs q) (htgt q)
    (hε _ (hw q) _ (hlift _)) t q (ht q)).app σ

end Langlands.Aubert.General.RationalPointFamily
