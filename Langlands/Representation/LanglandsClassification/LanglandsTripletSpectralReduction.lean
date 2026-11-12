import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityReduction
import Langlands.Representation.Intertwining.PQRegularityLemmaStatement
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # The remaining graded-exponent separation and its regularity consequence -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The nonidentity graded-piece exponent separation used in Renard VII.4.1,
read on the actual full geometric-lemma pieces, at arbitrary representative data. -/
def LanglandsTripletOppositePieceSeparationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (J : Set (characterLattice T)) (f : A ⟶ T)
      (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ψ : leviUnramifiedCharacters l hl)
      (Pbar Ubar : GroupScheme (Spec (CommRingCat.of k)))
      (pbar : Pbar ⟶ G) (lbar : M ⟶ Pbar) (rbar : Ubar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hlbar : IsRationalLeviSubgroup lbar)
      (hrbar : LeviSubgroup.IsGeometricUnipotentRadical rbar)
      (hmulbar : IsIso (subgroupMultiplication lbar rbar)),
      lbar ≫ pbar = l ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) →
      IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ →
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p l hp hl
        let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
        haveI := hl.isConnectedReductive.isAffineHom
        letI := RationalPointFamily.splitComponentPointTopology ha
        ∀ z : parabolicDoubleCosets p pbar → rationalPoints G,
          (∀ w, DoubleCoset.mk (pointImage p) (pointImage pbar) (z w) = w) →
          ∀ (E : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage pbar) w
              (identityParabolicDoubleCoset p pbar) →
              GeometricLemmaIntersectionDatum p l r hp hr hl hmul pbar lbar rbar
                hpbar hrbar hlbar hmulbar (z w)),
            ∀ w (h : Geometric.BruhatLT (pointImage p) (pointImage pbar) w
                (identityParabolicDoubleCoset p pbar)),
              Disjoint (groupExponents ha τ)
                {χ | IsGeneralizedWeight ((E w h).pieceFunctor.obj τ).ρ
                  (rationalPoints.map a) χ
                  ha.isCentralSplitTorus.isCentral.map_mem_center}

/-- The represented geometric lemma, the VII.3.3 regularity criterion, and the
Langlands-specific piece separation imply the exact kernel assertion. -/
def LanglandsTripletOppositeKernelReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    PQRegularityLemmaStatement.{u, v} →
      LanglandsTripletOppositePieceSeparationStatement.{u, v} →
        LanglandsTripletOppositeKernelStatement.{u, v}

/-- Reindex the finite representatives of the geometric lemma to actual double cosets,
then use the finite-length direction of the VII.3.3 criterion. -/
theorem langlandsTripletOppositeKernel_of_pieceSeparation :
    LanglandsTripletOppositeKernelReductionStatement.{u, v} := by
  intro hGL hPQ hSep k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i _ ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
    Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp hTrip
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  let : TopologicalSpace (rationalPoints A.toGrp) := RationalPointFamily.splitComponentPointTopology ha
  let τ := σ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)
  have hirr : τ.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hTrip.2.1
  obtain ⟨m, c, z, hz, E, _⟩ :=
    hGL k G hG P M U Pbar M Ubar p l r hp hl hr hmul
      pbar lbar rbar hpbar hlbar hrbar hmulbar
  let z' (w : parabolicDoubleCosets p pbar) := z (c.symm w)
  have hz' (w : parabolicDoubleCosets p pbar) :
      DoubleCoset.mk (pointImage p) (pointImage pbar) (z' w) = w :=
    (hz (c.symm w)).trans (c.apply_symm_apply w)
  let E' (w : parabolicDoubleCosets p pbar)
      (_ : Geometric.BruhatLT (pointImage p) (pointImage pbar) w
        (identityParabolicDoubleCoset p pbar)) := E (c.symm w)
  have hcriterion := hPQ k G hG P M U Pbar Ubar p l r hp hl hr hmul
    pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi.symm A a ha τ z' hz' E'
  exact hcriterion.2.2 (SmoothRep.hasFiniteLength_of_isIrreducible hirr)
    (hSep k G hG T i ν D P M U A p l r a hp hl hr hmul ha J f σ ψ
      Pbar Ubar pbar lbar rbar hpbar hlbar hrbar hmulbar hLevi hOpp hTrip z' hz' E')

/-- A complete explicit conditional route to the unchanged VII.4.1 target. -/
def LanglandsTripletOppositeSpectralReductionStatement : Prop :=
  OppositeIdentitySupportStatement.{u, v} →
    RepresentedGeometricLemmaStatement.{u, v} →
      PQRegularityLemmaStatement.{u, v} →
        LanglandsTripletOppositePieceSeparationStatement.{u, v} →
          LanglandsTripletOppositeRegularityStatement.{u, v}

/-- Assemble the spectral regularity and dimension reductions. -/
theorem langlandsTripletOppositeRegularity_of_pieceSeparation :
    LanglandsTripletOppositeSpectralReductionStatement.{u, v} := by
  intro hS hGL hPQ hSep
  exact langlandsTripletOppositeRegularity_of_kernel_and_identitySupport hS
    (langlandsTripletOppositeKernel_of_pieceSeparation hGL hPQ hSep)

end Langlands.Aubert.General.RepresentedParabolic
