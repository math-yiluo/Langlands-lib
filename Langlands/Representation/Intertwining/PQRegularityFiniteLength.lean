import Langlands.Representation.Intertwining.PQRegularityCriteria
import Langlands.Representation.Intertwining.PQFiniteLengthAction
import Langlands.Representation.Exponents.LeviJacquetFiniteLengthStatement
import Langlands.Representation.Exponents.LeviInductionFiniteLengthStatement
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof

/-! # Finite-length assembly for PQ regularity -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section PieceFiniteLength

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance finiteLengthPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- Full geometric pieces preserve finite length when the two parabolic
functors do. This theorem retains both global preservation premises. -/
theorem GeometricLemmaIntersectionDatum.pieceFunctor_finiteLength
    (hJacquet : LeviJacquetFiniteLengthStatement.{u, v})
    (hInduction : LeviInductionFiniteLengthStatement.{u, v})
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl; σ.HasFiniteLength) :
    IsFiniteLength (MonoidAlgebra ℂ (rationalPoints L)) (D.pieceFunctor.obj σ).ρ.asModule := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have hJ := hJacquet k M hl.isConnectedReductive D.P' D.M' D.N'
    D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' σ hσ
  have hT := SmoothRep.pullbackFunctor_preservesFiniteLength D.e _ hJ
  exact hInduction k L hlQ.isConnectedReductive D.Q' D.L' D.U'
    D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ' _ hT

/-- Finite length gives a finite faithful split-component action algebra on
an actual Levi, using its canonical second-countable locally compact topology. -/
theorem finite_splitComponent_actionQuotient
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
    (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hσ : letI := leviPointTopology l hl; σ.HasFiniteLength) :
    letI := leviPointTopology l hl
    Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (σ.representation.comp (rationalPoints.map a))) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_locallyCompactSpace k M
  have : IsTopologicalGroup (rationalPoints M) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup k M
  have : SecondCountableTopology (rationalPoints M) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology k M
  have : SigmaCompactSpace (rationalPoints M) := inferInstance
  let c : rationalPoints A.toGrp →* Subgroup.center (rationalPoints M) :=
    (rationalPoints.map a).codRestrict _ ha.isCentralSplitTorus.isCentral.map_mem_center
  exact PQFiniteLengthAction.finite_actionQuotient σ.representation c σ.isSmooth hσ

end PieceFiniteLength

/-- Conditional assembly of the exact regularity statement. The two global
finite-length preservation statements remain explicit mathematical premises. -/
def PQRegularityFiniteLengthReductionStatement : Prop :=
  LeviJacquetFiniteLengthStatement.{u, v} →
    LeviInductionFiniteLengthStatement.{u, v} → PQRegularityLemmaStatement.{u, v}

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- The exact regularity conclusion follows from finite-length preservation by
the represented Jacquet and induction functors. The premises remain explicit. -/
theorem pqRegularity_finiteLength_reduction :
    PQRegularityFiniteLengthReductionStatement.{u, v} := by
  intro hJacquet hInduction k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let ambientTopology : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := RationalPointFamily.splitComponentPointTopology ha
  intro σ z hz D
  have hc := pqRegularity_predecessorCriteria.{u, v} k G hG
    P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha σ z hz D
  refine ⟨hc.1, hc.2, ?_⟩
  intro hσ hdisjoint
  obtain ⟨n, c, s, he⟩ := exists_pqRegularity_pieceFiltration.{u, v} k G hG
    P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame z hz D
  let pieces := fun i : Fin n => (D (c i).val (c i).property).pieceFunctor
  let e : ∀ i, s.graded i ≅ pieces i := fun i => (he i).some
  have hsmooth : ∀ i, IsSmooth ((pieces i).obj σ).ρ :=
    fun i => (D (c i).val (c i).property).pieceFunctor_isSmooth σ
  let : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (σ.representation.comp (rationalPoints.map a))) :=
    finite_splitComponent_actionQuotient (l := l) (hl := hl) A a ha σ hσ
  have hfinite (i : Fin n) : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (((pieces i).obj σ).ρ.comp (rationalPoints.map a))) := by
    let τ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M) :=
      SmoothRep.of ((pieces i).obj σ).ρ (hsmooth i)
    have hτ : τ.HasFiniteLength :=
      (D (c i).val (c i).property).pieceFunctor_finiteLength hJacquet hInduction σ hσ
    exact finite_splitComponent_actionQuotient (l := l) (hl := hl) A a ha τ hτ
  let : ∀ i, Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (((pieces i).obj σ).ρ.comp (rationalPoints.map a))) := hfinite
  apply pqRegularity_of_disjoint_weights p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    a s pieces e σ ha hsmooth
  intro i
  exact hdisjoint (c i).val (c i).property

end Langlands.Aubert.General.RepresentedParabolic
