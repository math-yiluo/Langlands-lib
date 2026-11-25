/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteTracePresentation.DiagonalFiniteTraceChernCriterion
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerChernNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceTwistedSplittingComponents
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleFaithful

/-! # The Chern degree of the reduced completed trace

Source: diagonal tower coefficient changes paragraph (1), and trace paragraph (1).
(blueprint: lem-diagonal-uniformizer-trace-chern-degree).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization.iso Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

attribute [local semireducible] UniformizerChernNormalizationData.ChernNormalized

private theorem completedChern_trace
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (c : DiagonalTrace.completedUnit l S ⟶
      tq.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (hc : (diagonalCompletedUnderlying l S).map c ≫
        tq.toPresentation.sourceMap l (ULift.{u} (Padic l)) =
      tq.coefficientsS.unitMap l (ULift.{u} (Padic l)) tq.LS ≫
        tq.LS.R.map (tq.toPresentation.systemChern l)) : c ≫ tq.trace = 𝟙 _ := by
  let E := ULift.{u} (Padic l)
  let p := tq.toPresentation
  let T := p.twistS.T l E ⋙
    shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S)) (2 : ℤ)
  let b := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (2 : ℤ)).mapIso
        (((p.twistS.T l E).commShiftIso (-2 : ℤ)).app
          (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    (shiftFunctorCompIsoId (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (-2 : ℤ) 2 (by decide)).app
        ((p.twistS.T l E).obj (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    p.twistS.contract l E
  obtain ⟨_, _, hchern⟩ := DiagonalTrace.diagonalTrace_twistedSplitting_components l p hS
  change p.model.chernAdjoint l E = b.inv ≫ T.map biprod.inr ≫
    T.map (p.model.bq l E) ≫ (p.model.twistedPush l E).hom at hchern
  have ht : p.model.trace l E = (p.model.twistedPush l E).inv ≫
      T.map (inv (p.model.bq l E)) ≫ T.map biprod.snd ≫ b.hom := by rfl
  have hmodel : p.model.chernAdjoint l E ≫ p.model.trace l E = 𝟙 _ := by
    calc
      _ = b.inv ≫ T.map
          (biprod.inr ≫ p.model.bq l E ≫ inv (p.model.bq l E) ≫ biprod.snd) ≫
            b.hom := by
        rw [hchern, ht]
        simp only [Functor.map_comp, Category.assoc,
          (p.model.twistedPush l E).hom_inv_id_assoc]
      _ = 𝟙 _ := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inr_snd, CategoryTheory.Functor.map_id]
        exact (congrArg (b.inv ≫ ·) (Category.id_comp b.hom)).trans b.inv_hom_id
  have hsystem : p.systemChern l ≫ p.systemTrace l E = 𝟙 _ := by
    unfold DiagonalTrace.Presentation.systemChern DiagonalTrace.Presentation.systemTrace
    change (p.restrictionS.F.mapDerivedCategory.map (p.model.chernAdjoint l E) ≫
        p.varying.hom.app ((SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧)) ≫
      (p.varying.inv.app ((SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧) ≫
        p.restrictionS.F.mapDerivedCategory.map (p.model.trace l E)) = 𝟙 _
    rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      hmodel, CategoryTheory.Functor.map_id]
  have htrace : (diagonalCompletedUnderlying l S).map tq.trace ≫
      p.coefficientsS.unitMap l E p.LS = p.sourceMap l E ≫
        p.LS.R.map (p.systemTrace l E) := by
    simpa only [DiagonalTrace.Presentation.IsTrace, DiagonalTrace.Presentation.sourceMap,
      Category.assoc] using tq.construction
  have := tq.unit_limit
  apply DiagonalTrace.diagonalTrace_single_map_injective l S
  apply (cancel_mono (p.coefficientsS.unitMap l E p.LS)).mp
  calc
    _ = (diagonalCompletedUnderlying l S).map c ≫
        ((diagonalCompletedUnderlying l S).map tq.trace ≫
          p.coefficientsS.unitMap l E p.LS) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ((diagonalCompletedUnderlying l S).map c ≫ p.sourceMap l E) ≫
        p.LS.R.map (p.systemTrace l E) := by rw [htrace, Category.assoc]
    _ = (p.coefficientsS.unitMap l E p.LS ≫ p.LS.R.map (p.systemChern l)) ≫
        p.LS.R.map (p.systemTrace l E) := by rw [hc]
    _ = p.coefficientsS.unitMap l E p.LS := by
      rw [Category.assoc, ← Functor.map_comp, hsystem,
        CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := by rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The reduced trace has degree one on the canonical positive Kummer Chern
summand. This is an endomorphism equation of the finite coefficient unit, and
asserts nothing about the positive-line summand or equality of entire traces.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), coefficient reduction;
sk-prop-diagonal-tower-trace.proof.md, paragraph (1), finite trace projection.
(blueprint: lem-diagonal-uniformizer-trace-chern-degree).

Proof: lift the strict-system Chern adjunct to completed coefficients using
fullness on derived-complete objects. The positive twisted-splitting component
and the definition of its inverse trace give Chern followed by trace equal to
one in the system category. The lift and trace normalizations transport this
equation to constant coefficients; degree-zero faithfulness gives it over the
completed ring. The coefficient normalization of the positive Chern adjunct is
isolated in diagonalUniformizer_chernNormalization. Compose q_trace with the
two scalar trace squares and the finite presentation comparison. These identify
the finite trace factor with the image of the completed trace. Applying the
coefficient functor to the completed Chern/trace equation and cancelling the
coefficient-unit isomorphism proves the result. Only the positive Chern arrow
needs geometric comparison. No detection of arbitrary derived arrows by finite
levels is used. Exponent n+1 is positive at n=0, hA handles ramification, and
the construction includes the empty scheme. -/
theorem diagonalUniformizer_traceChernDegree
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (zl : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l))
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    (integral : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
      (fun X ↦ spIntegralTwist X l E))
    (toIntegral : ScalarCompatibility (integralMap l E) Y (zlLine l)
      (fun X ↦ spIntegralTwist X l E) (integralLineMap l E) zl integral)
    (tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y))
    (completedY : CompletedRealization l Y)
    (completedP : CompletedRealization l (ProjectiveLine Y))
    (q_model : tq.model.model = Iso.refl (ProjectiveLine Y))
    (q_square : CompletedPushSquare l (ProjectiveLine Y ↘ Y)
      completedP completedY tq.Rc zl.Rq)
    (q_trace : CompletedTraceCompatibility l (ProjectiveLine Y ↘ Y)
      completedP completedY tq zl.Rq q_square zl.traceq)
    [hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))]
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) integral d)
    (eY : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y)
    (eP : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (lineP : QuotientLineRealization l E π n n hA (ProjectiveLine Y) eP)
    (presentation : FiniteTracePresentation
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow
      (quotientLine l E π n) d eY eP) :
    FiniteTraceChernDegree
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow
      (quotientLine l E π n) d eY eP (lineP.iso l) presentation := by
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    apply (isUnit_pow_iff (Nat.succ_ne_zero n)).mp
    simpa only [Nat.cast_pow] using hYpow
  obtain ⟨c, hc⟩ := DiagonalTrace.diagonalTrace_completedChern_lift l tq.toPresentation hY
  have hct := completedChern_trace l tq hY c hc
  let normalizationData : UniformizerChernNormalizationData l Y :=
    { zl := zl
      E := E
      π := π
      n := n
      hπ := hπ
      integral := integral
      toIntegral := toIntegral
      tq := tq
      completedY := completedY
      completedP := completedP
      q_model := q_model
      q_square := q_square
      hfinite := hfinite
      hA := hA
      hYpow := hYpow
      d := d
      scalar := scalar
      eY := eY
      eP := eP
      lineP := lineP
      presentation := presentation
      c := c
      hc := hc }
  exact (normalizationData.diagram l Y).traceDegree
    (diagonalUniformizer_chernNormalization l Y normalizationData) hct q_trace

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
