import Langlands.Representation.Geometric.RepresentedParabolicSupportFiltration
import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryStatement
import Langlands.Representation.Geometric.CosetOrbitOrdering
import Langlands.Topology.GroupAction.FiniteOrbitProof
import Langlands.Representation.Aubert.General.RationalPointSecondCountable

/-! # Normalized support grades for arbitrary represented parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The natural normalized comparison for the fixed support-image filtration:
each successive quotient is the intersection piece at the same orbit. -/
def RepresentedGeometricLemmaSupportGradedStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q L U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ))
      (m : ℕ) (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m)
      (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ (s.representative i)⁻¹),
      (leviJacquetSupportFiltration.{u, v} p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ s).HasGradedPieces (fun i => (D i).pieceFunctor)

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Geometry and the fixed-support normalized comparison imply the exact full
represented geometric lemma, without additional topological hypotheses. -/
theorem representedGeometricLemma_of_geometry_and_supportGraded
    (hgeometry : RepresentedGeometricLemmaGeometryStatement.{u})
    (hgraded : RepresentedGeometricLemmaSupportGradedStatement.{u, v}) :
    RepresentedGeometricLemmaStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  obtain ⟨m, c, z, hz, ⟨D⟩⟩ :=
    hgeometry k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hfinite : Finite (DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage q : Set (rationalPoints G))) :=
    Finite.of_surjective c c.surjective
  obtain ⟨n, ⟨s⟩⟩ :=
    (Geometric.closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (rationalPoints G) (pointImage p) (pointImage q)
        (isClosed_pointImage p hp.isClosedSubgroup)
        (isClosed_pointImage q hq.isClosedSubgroup) hfinite
  have hbij : Function.Bijective
      (fun i : Fin m => DoubleCoset.mk (pointImage p) (pointImage q) ((z i)⁻¹)⁻¹) := by
    simpa only [inv_inv, hz] using c.bijective
  obtain ⟨e, t, ht⟩ := s.classifiedRepresentatives (fun i : Fin m => (z i)⁻¹) hbij
  let E : ∀ i : Fin n, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (t.representative i)⁻¹ := fun i => by
    rw [ht i, inv_inv]
    exact D (e i)
  let F := leviJacquetSupportFiltration.{u, v} p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ t
  have hF : F.HasGradedPieces (fun i => (E i).pieceFunctor.{u, v}) :=
    hgraded k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ n t E
  clear_value E F
  refine ⟨n, t.doubleCosetEquiv, fun i => (t.representative i)⁻¹, fun _ => rfl, E, ?_⟩
  refine ⟨Equiv.refl _, F, ?_⟩
  intro i
  simpa only [Function.comp_apply, Equiv.refl_apply] using hF i

end Langlands.Aubert.General.RepresentedParabolic
