/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedFrame
import WeilConjectures.CategoryTheory.SixFunctors.IntegrationTransport

/-! # Condensed realization of the completed diagonal diagram

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-completed-diagram-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem shiftedLine_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X) :
    IsIso (e.shiftedLine l X) := by
  dsimp only [CompletedRealization.shiftedLine]
  infer_instance

private theorem singleUnit_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X) :
    IsIso (e.singleUnit l X) := by
  dsimp only [CompletedRealization.singleUnit]
  infer_instance

/-- Realize a completed diagonal diagram as a condensed Z_l diagram, without
performing any extension of coefficient fields or quotient reduction.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), initial Z_l stage.
(blueprint: lem-diagonal-completed-diagram-realization).

Proof: The normalized integral coefficient limit at the bottom finite field
identifies the completed coefficient ring with the pulled-back condensed Z_l
ring. Internal abelian module sheaves and sectionwise module sheaves are
equivalent, retaining their underlying sheaves. Transport along this ring
comparison gives exact equivalences on Y, P and W. The coefficient projections
normalize the regular module comparisons, and the root-limit projections
normalize the positive-line comparisons. Direct image retains the underlying
sheaf, so these equivalences give ordinary direct-image squares. Their unique
right-derived extensions are fixed by the full universal units. Use these
squares to transport δ, the three given traces, and the two supported sources.
Naturality of the squares and the two assumed integration equalities prove
integration for the transported diagram. The supported-source and root
normalizations are preserved by construction. The resulting Reference only
uses the Z_l component of a family, so it applies to every family having this
component. This construction does not claim that separate finite reductions
detect arbitrary derived morphisms. -/
theorem diagonalCompletedDiagram_realization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y))
    (t₁ : DiagonalTrace.Result l (ULift.{u} (Padic l))
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (t₂ : DiagonalTrace.Result l (ULift.{u} (Padic l))
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (hq : tq.model.model = Iso.refl (ProjectiveLine Y))
    (h₁ : t₁.model.model = diagonalTraceFirstModel Y)
    (h₂ : t₂.model.model = diagonalTraceSecondModel Y)
    (a₁ : DiagonalTrace.SupportedSource l Y
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₁.Rc)
    (a₂ : DiagonalTrace.SupportedSource l Y
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₂.Rc)
    (hi₁ : DiagonalTrace.IsIntegration t₁.Rc.R a₁.hom t₁.trace δ)
    (hi₂ : DiagonalTrace.IsIntegration t₂.Rc.R a₂.hom t₂.trace δ) :
    ∃ d : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l),
      ∀ family : Family l Y, family.zl = d → Nonempty (Reference l Y δ family) := by
  obtain ⟨rootsY⟩ := Nonempty.intro (diagonalIntegralRoots l Y (bottomField l))
  obtain ⟨rootsP⟩ := Nonempty.intro (diagonalIntegralRoots l (ProjectiveLine Y) (bottomField l))
  obtain ⟨rootsW⟩ :=
    Nonempty.intro (diagonalIntegralRoots l (diagonalSurface Y) (bottomField l))
  obtain ⟨e⟩ := diagonalCompleted_frame l Y hY rootsY rootsP rootsW tq t₁ t₂ a₁ a₂
  let Rq := condensedDiagonalRightDerived l (ProjectiveLine Y ↘ Y)
  let R₁ := condensedDiagonalRightDerived l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let R₂ := condensedDiagonalRightDerived l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let sq := e.q_ordinary.derive (R := tq.Rc) (R' := Rq)
  let s₁ := e.p₁_ordinary.derive (R := t₁.Rc) (R' := R₁)
  let s₂ := e.p₂_ordinary.derive (R := t₂.Rc) (R' := R₂)
  let U := e.eW.F.mapDerivedCategory
  let V := e.eP.F.mapDerivedCategory
  let S := (DerivedCategory.singleFunctor
    (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y)) 0)
  let source := (e.eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    S.map e.sourceIso.hom
  let delta := S.map e.sourceIso.inv ≫ SpTowerClasses.mapSingleArrow e.eW.F (2 : ℤ) δ ≫
    (S.map e.eW.lineIso.hom)⟦(2 : ℤ)⟧'
  let := shiftedLine_isIso l (diagonalSurface Y) e.eW
  let := shiftedLine_isIso l (ProjectiveLine Y) e.eP
  let := singleUnit_isIso l Y e.eY
  let := singleUnit_isIso l (ProjectiveLine Y) e.eP
  let traceq := inv (sq.derived.iso.hom.app _ ≫
    Rq.R.map (e.eP.shiftedLine l (ProjectiveLine Y))) ≫
      e.eY.F.mapDerivedCategory.map tq.trace ≫ e.eY.singleUnit l Y
  let trace₁ := inv (s₁.derived.iso.hom.app _ ≫
    R₁.R.map (e.eW.shiftedLine l (diagonalSurface Y))) ≫
      V.map t₁.trace ≫ e.eP.singleUnit l (ProjectiveLine Y)
  let trace₂ := inv (s₂.derived.iso.hom.app _ ≫
    R₂.R.map (e.eW.shiftedLine l (diagonalSurface Y))) ≫
      V.map t₂.trace ≫ e.eP.singleUnit l (ProjectiveLine Y)
  have hdelta : U.map δ ≫ e.eW.shiftedLine l (diagonalSurface Y) =
      source ≫ delta := by
    dsimp only [source, delta, SpTowerClasses.mapSingleArrow,
      CompletedRealization.shiftedLine, U, S]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
    simp
  have htraceq : CompletedTraceCompatibility l (ProjectiveLine Y ↘ Y)
      e.eP e.eY tq Rq sq traceq := by
    dsimp only [CompletedTraceCompatibility, traceq]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₁ : CompletedTraceCompatibility l
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      e.eW e.eP t₁ R₁ s₁ trace₁ := by
    dsimp only [CompletedTraceCompatibility, trace₁, V]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₂ : CompletedTraceCompatibility l
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      e.eW e.eP t₂ R₂ s₂ trace₂ := by
    dsimp only [CompletedTraceCompatibility, trace₂, V]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  let d : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l) :=
    { Rq := Rq
      R₁ := R₁
      R₂ := R₂
      q_canonical := rfl
      p₁_canonical := rfl
      p₂_canonical := rfl
      q_unit := by
        intro K
        exact Category.comp_id _
      p₁_unit := by
        intro K
        exact Category.comp_id _
      p₂_unit := by
        intro K
        exact Category.comp_id _
      delta := delta
      traceq := traceq
      trace₁ := trace₁
      trace₂ := trace₂
      support₁ := e.support₁
      support₂ := e.support₂
      integration₁ := integration_transport t₁.Rc.R R₁.R U V
        s₁.derived.iso.hom source (e.eW.shiftedLine l (diagonalSurface Y))
        (asIso (e.eP.singleUnit l (ProjectiveLine Y))) a₁.hom δ t₁.trace
        e.support₁.hom delta trace₁ e.source₁ hdelta htrace₁ hi₁
      integration₂ := integration_transport t₂.Rc.R R₂.R U V
        s₂.derived.iso.hom source (e.eW.shiftedLine l (diagonalSurface Y))
        (asIso (e.eP.singleUnit l (ProjectiveLine Y))) a₂.hom δ t₂.trace
        e.support₂.hom delta trace₂ e.source₂ hdelta htrace₂ hi₂ }
  refine ⟨d, fun family hf ↦ ?_⟩
  cases family with
  | mk zl integral rational closure toIntegral toRational toClosure rationalTransitions =>
    dsimp only [Family.zl] at hf
    subst zl
    exact ⟨{
      eY := e.eY, eP := e.eP, eW := e.eW
      sourceIso := e.sourceIso, source_normalization := e.source_normalization
      delta := rfl
      tq := tq, t₁ := t₁, t₂ := t₂
      q_model := hq, p₁_model := h₁, p₂_model := h₂
      q_square := sq, p₁_square := s₁, p₂_square := s₂
      q_trace := htraceq, p₁_trace := htrace₁, p₂_trace := htrace₂ }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
