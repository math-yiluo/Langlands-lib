import Langlands.Representation.Intertwining.PQPredecessorFiltration
import Langlands.Representation.Intertwining.PQRegularityLemmaStatement

/-! # The kernel and forward-exponent clauses of Renard VII.3.3 -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section PieceSmoothness

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance criteriaPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- Every full geometric piece is smooth for the original target Levi action. -/
theorem GeometricLemmaIntersectionDatum.pieceFunctor_isSmooth
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology lQ hlQ
    IsSmooth (D.pieceFunctor.obj σ).ρ := by
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
  exact ((leviInductionFunctor D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ').obj
    ((SmoothRep.pullbackFunctor D.e).obj
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ))).isSmooth

end PieceSmoothness

private theorem iInf_equiv_subtype {Index Grade Carrier : Type*} [CompleteLattice Carrier]
    {p : Index → Prop} (c : Grade ≃ {x // p x}) (f : ∀ x, p x → Carrier) :
    (⨅ i, f (c i).val (c i).property) = ⨅ (x) (hx), f x hx := by
  exact (c.iInf_comp (g := fun w => f w.val w.property)).trans iInf_subtype

/-- The unconditional kernel criterion and forward exponent implication, on all
supplied full geometric pieces at the strict predecessors of identity. -/
def PQRegularityPredecessorCriteriaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
        (ha : IsSplitComponent a),
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        haveI := leviPoints_nonarchimedeanGroup p l hp hl
        letI := RationalPointFamily.splitComponentPointTopology ha
        ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
          (z : parabolicDoubleCosets p q → rationalPoints G),
          (∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (z w) = w) →
          ∀ (D : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
              (identityParabolicDoubleCoset p q) →
              GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (z w)),
            (IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ ↔
                splitComponentKernel l hl a σ ⊔
                  (⨅ (w) (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
                    (identityParabolicDoubleCoset p q)),
                    pieceSplitComponentKernel a (D w h) σ) = ⊤) ∧
              (IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ →
                ∀ w (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
                  (identityParabolicDoubleCoset p q)),
                  Disjoint (groupExponents ha σ)
                    {χ | IsGeneralizedWeight ((D w h).pieceFunctor.obj σ).ρ
                      (rationalPoints.map a) χ
                      ha.isCentralSplitTorus.isCentral.map_mem_center})

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- The first two clauses of the regularity lemma. -/
theorem pqRegularity_predecessorCriteria : PQRegularityPredecessorCriteriaStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let ambientTopology : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := RationalPointFamily.splitComponentPointTopology ha
  intro σ z hz D
  obtain ⟨n, c, s, he⟩ := exists_pqRegularity_pieceFiltration.{u, v} k G hG
    P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame z hz D
  let pieces := fun i : Fin n => (D (c i).val (c i).property).pieceFunctor
  let e : ∀ i, s.graded i ≅ pieces i := fun i => (he i).some
  have hk : (⨅ i, groupAlgebraKernel ((pieces i).obj σ).ρ (rationalPoints.map a)) =
      ⨅ (w) (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q)), pieceSplitComponentKernel a (D w h) σ := by
    change (⨅ i, pieceSplitComponentKernel a (D (c i).val (c i).property) σ) = _
    exact iInf_equiv_subtype (Carrier := Ideal (MonoidAlgebra ℂ (rationalPoints A.toGrp)))
      c (fun w h => pieceSplitComponentKernel a (D w h) σ)
  constructor
  · rw [← hk]
    exact pqRegularity_iff_pieceKernels p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      a s pieces e σ
  · intro hreg
    have hsmooth : ∀ i, IsSmooth ((pieces i).obj σ).ρ :=
      fun i => (D (c i).val (c i).property).pieceFunctor_isSmooth σ
    have hweights := pqRegularity_disjoint_weights.{u, v}
      p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a s pieces e σ ha hsmooth hreg
    change ∀ i, Disjoint (groupExponents ha σ)
      {χ | IsGeneralizedWeight ((D (c i).val (c i).property).pieceFunctor.obj σ).ρ
        (rationalPoints.map a) χ ha.isCentralSplitTorus.isCentral.map_mem_center} at hweights
    have hindex : ∀ t : {w | Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q)}, Disjoint (groupExponents ha σ)
        {χ | IsGeneralizedWeight ((D t.val t.property).pieceFunctor.obj σ).ρ
          (rationalPoints.map a) χ ha.isCentralSplitTorus.isCentral.map_mem_center} := by
      intro t
      obtain ⟨i, rfl⟩ := c.surjective t
      unfold ambientTopology
      set_option backward.isDefEq.respectTransparency.types true in
        with_reducible exact hweights i

    unfold ambientTopology at hindex
    intro w hw
    have hmem : w ∈ {w | Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q)} := hw
    set_option backward.isDefEq.respectTransparency.types true in
      with_reducible exact hindex ⟨w, hmem⟩

end Langlands.Aubert.General.RepresentedParabolic
