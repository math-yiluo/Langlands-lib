import Langlands.Representation.Intertwining.PQRegularityFiniteLength
import Langlands.Representation.Intertwining.PieceActionQuotientFiniteness
import Langlands.Representation.Exponents.GeometricLemmaSplitComponent
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeProof
import Langlands.Representation.Aubert.General.PrerequisiteStatements

/-! # The `PQ`-regularity lemma from finite-length admissibility

Renard VII.3.3 needs, for its third assertion, that the split component `A_M` acts on every
graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}(σ)` of a finite-length `σ` through a
finite-dimensional quotient of its group algebra. This module derives that finiteness from the
admissibility of finite-length representations of `M(F)` alone, using the proved
admissibility (VI.6.1) and finite type (VI.1.3) of Jacquet modules. The finite-length
admissibility statement remains an explicit premise.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Finite-length admissibility for connected reductive groups (Renard VI.6.3, one
direction) implies the exact `PQ`-regularity lemma (Renard VII.3.3). -/
def PQRegularityAdmissibleReductionStatement : Prop :=
  RationalPointsFiniteLengthAdmissibleStatement.{u, v} → PQRegularityLemmaStatement.{u, v}

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- The exact regularity conclusion follows from the admissibility of finite-length
representations of connected reductive groups. That admissibility remains an explicit
premise; Jacquet admissibility and Jacquet finite type are imported proofs. -/
theorem pqRegularity_admissible_reduction :
    PQRegularityAdmissibleReductionStatement.{u, v} := by
  intro hAdmissible k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let ambientTopology : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  have hM := hl.isConnectedReductive
  have := hM.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
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
  have hσadm : σ.IsAdmissible := hAdmissible k M hM σ hσ
  have hσfg : Module.Finite (MonoidAlgebra ℂ (rationalPoints M))
      σ.representation.asModule := by
    have : IsNoetherian (MonoidAlgebra ℂ (rationalPoints M)) σ.representation.asModule :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hσ).1
    infer_instance
  have hpiece : ∀ (w) (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
      (identityParabolicDoubleCoset p q)),
      Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
        (((D w h).pieceFunctor.obj σ).ρ.comp (rationalPoints.map a))) := by
    intro w h
    generalize D w h = E
    let := leviPointTopology E.l' E.hl'
    obtain ⟨b, hb, -⟩ := E.exists_isCentralSplitTorus_factor ha.1
    have hJa : ((leviJacquetFunctor E.p' E.l' E.r' E.hp' E.hr' E.hl' E.hmul').obj
        σ).IsAdmissible :=
      isAdmissible_comp_continuousMulEquiv
        ((jacquetFunctor E.p' E.l' E.r' E.hp' E.hr' E.hl' E.hmul').obj σ).representation
        (leviPointsEquiv E.p' E.l' E.hp' E.hl')
        (arbitraryParabolicJacquetAdmissibility.{u, v} k M hM E.P' E.M' E.N' E.p' E.l'
          E.r' E.hp' E.hl' E.hr' E.hmul' σ hσadm)
    have hJf : Module.Finite (MonoidAlgebra ℂ (rationalPoints E.M'))
        ((leviJacquetFunctor E.p' E.l' E.r' E.hp' E.hr' E.hl' E.hmul').obj
          σ).representation.asModule :=
      leviJacquetFiniteType.{u, v} k M hM E.P' E.M' E.N' E.p' E.l' E.r'
        E.hp' E.hl' E.hr' E.hmul' σ hσfg
    exact E.finite_actionQuotient_piece ha b hb σ hJa hJf
  have hfinite (i : Fin n) : Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (((pieces i).obj σ).ρ.comp (rationalPoints.map a))) :=
    hpiece (c i).val (c i).property
  let : ∀ i, Module.Finite ℂ (PQFiniteActionRegularity.actionQuotient
      (((pieces i).obj σ).ρ.comp (rationalPoints.map a))) := hfinite
  apply pqRegularity_of_disjoint_weights p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    a s pieces e σ ha hsmooth
  intro i
  exact hdisjoint (c i).val (c i).property

end Langlands.Aubert.General.RepresentedParabolic
