import Langlands.Representation.LanglandsClassification.LanglandsTripletOppositePieceSeparation
import Langlands.Representation.Intertwining.OppositeIdentitySupportProof
import Langlands.Representation.Intertwining.PQRegularityFiniteLength
import Langlands.Representation.Intertwining.PieceActionQuotientFiniteness
import Langlands.Representation.Exponents.GeometricLemmaSplitComponent
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.Smooth.IsotypicProjector

/-! # `PP̄`-regularity of Langlands triplets (Renard VII.4.1, Lemma): proof -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.PQFiniteActionRegularity

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance tripletRegularityPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- A split component of the common Levi acts on the full geometric-lemma piece of an
irreducible admissible representation through a finite-dimensional quotient of its group
algebra. -/
theorem finite_actionQuotient_piece_of_irreducible
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M), σ.IsIrreducible → σ.IsAdmissible →
      Module.Finite ℂ (actionQuotient ((D.pieceFunctor.obj σ).ρ.comp (rationalPoints.map a))) := by
  have hM := hl.isConnectedReductive
  have := hM.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ hirr hadm
  obtain ⟨A', a', f, -, hf⟩ := D.exists_isSplitComponent_factor ha
  have hb : (f ≫ a') ≫ D.lQ' ≫ D.q' = a := by
    simpa only [Category.assoc] using hf
  refine D.finite_actionQuotient_piece ha _ hb σ ?_ ?_
  · exact isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).representation
      (leviPointsEquiv D.p' D.l' D.hp' D.hl')
      (arbitraryParabolicJacquetAdmissibility.{u, v} k M hM D.P' D.M' D.N' D.p' D.l' D.r'
        D.hp' D.hl' D.hr' D.hmul' σ hadm)
  · exact leviJacquetFiniteType.{u, v} k M hM D.P' D.M' D.N' D.p' D.l' D.r' D.hp' D.hl' D.hr'
      D.hmul' σ (moduleFinite_asModule_of_isIrreducible σ.representation hirr)

end GeometricLemmaIntersectionDatum

/-- The kernel clause of Renard VII.4.1, Lemma: the inducing twist of a Langlands triplet is
`PP̄`-regular. The finite-dimensionality of the action quotients comes from irreducibility
and admissibility, not from finite-length preservation. -/
theorem langlandsTripletOppositeKernel : LanglandsTripletOppositeKernelStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
    Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology ha
  let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
  have hirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.1
  have hadm : τ.IsAdmissible :=
    (SmoothRep.isAdmissible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.2.1.isAdmissible
  obtain ⟨m, c₀, z, hz, E, -⟩ :=
    representedGeometricLemma.{u, v} k G hG P M U Pbar M Ubar p l r hp hl hr hmul
      pbar lbar rbar hpbar hlbar hrbar hmulbar
  let z' : parabolicDoubleCosets p pbar → rationalPoints G := fun w => z (c₀.symm w)
  have hz' : ∀ w, DoubleCoset.mk (pointImage p) (pointImage pbar) (z' w) = w :=
    fun w => (hz _).trans (c₀.apply_symm_apply w)
  let E' : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage pbar) w
      (identityParabolicDoubleCoset p pbar) →
      GeometricLemmaIntersectionDatum p l r hp hr hl hmul pbar lbar rbar
        hpbar hrbar hlbar hmulbar (z' w) :=
    fun w _ => E (c₀.symm w)
  obtain ⟨n, cc, s, he⟩ := exists_pqRegularity_pieceFiltration.{u, v} k G hG
    P M U Pbar Ubar p l r hp hl hr hmul pbar lbar rbar hpbar hlbar hrbar hmulbar
    hLevi.symm z' hz' E'
  let pieces := fun j : Fin n => (E' (cc j).val (cc j).property).pieceFunctor
  let e : ∀ j, s.graded j ≅ pieces j := fun j => (he j).some
  have hsmooth : ∀ j, IsSmooth ((pieces j).obj τ).ρ :=
    fun j => (E' (cc j).val (cc j).property).pieceFunctor_isSmooth τ
  have : Module.Finite ℂ (actionQuotient (τ.representation.comp (rationalPoints.map a))) :=
    finite_splitComponent_actionQuotient (l := l) (hl := hl) A a ha τ
      (SmoothRep.hasFiniteLength_of_isIrreducible hirr)
  have : ∀ j, Module.Finite ℂ (actionQuotient
      (((pieces j).obj τ).ρ.comp (rationalPoints.map a))) := fun j =>
    (E' (cc j).val (cc j).property).finite_actionQuotient_piece_of_irreducible ha τ hirr hadm
  apply pqRegularity_of_disjoint_weights p l r hp hr hl hmul pbar lbar rbar hpbar hrbar hlbar
    hmulbar a s pieces e τ ha hsmooth
  intro j
  exact langlandsTripletOppositePieceSeparation.{u, v} k G hG T i ν D P M U A p l r a
    hp hl hr hmul ha J f σ ψ Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp
    hTrip z' hz' E' (cc j).val (cc j).property

/-- Renard VII.4.1, Lemma: for a Langlands triplet `(P = MN, σ, ψ)` and an opposite
parabolic `P̄`, the twist `σ ⊗ ψ` is `PP̄`-regular and the intertwining maps
`i_P^G(σ ⊗ ψ) → i_{P̄}^G(σ ⊗ ψ)` form a complex vector space of finrank one. -/
theorem langlandsTripletOppositeRegularity :
    LanglandsTripletOppositeRegularityStatement.{u, v} :=
  langlandsTripletOppositeRegularity_of_kernel_and_identitySupport oppositeIdentitySupport
    langlandsTripletOppositeKernel

end Langlands.Aubert.General.RepresentedParabolic
