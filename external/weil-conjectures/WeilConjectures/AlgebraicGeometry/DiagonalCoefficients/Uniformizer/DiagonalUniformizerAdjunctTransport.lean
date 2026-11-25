/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerAdjunctConditions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedAdjunctSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ChernCoefficientDiagram.DiagonalCoefficientAdjunctAssembly

/-! # Transport of the canonical completed Chern adjunct

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Endpoint.shift Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit
  FiniteRealization.shiftedLine QuotientLineRealization.shifted
  QuotientLineRealization.iso

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

private theorem uniformizerLocalArrow
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧) :
    ChernCoefficientDiagram.localAdjunctArrow l Y (s.diagram l Y) z =
      (s.localUnitInv l Y ≫ (s.localFunctor l Y).map z) ≫ s.localLine l Y := by
  delta ChernCoefficientDiagram.localAdjunctArrow
    UniformizerChernNormalizationData.localUnitInv
    UniformizerChernNormalizationData.localFunctor
    UniformizerChernNormalizationData.localLine
    QuotientLineRealization.shifted
  -- Generalize the irreducible unit inverse syntactically: elaborating its
  -- large coefficient record again is unnecessary for associativity.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let isUnitInverse := fun (e : Lean.Expr) =>
      match e.getAppArgs.back? with
      | some i => e.isAppOf ``CategoryTheory.Iso.inv &&
          i.isAppOf ``ChernCoefficientDiagram.localUnitIso
      | none => false
    let some unitInverse := target.find? isUnitInverse |
      Lean.throwError "The specified unit inverse was not found"
    let unitType ← Lean.Meta.inferType unitInverse
    let marker := Lean.mkFVar (← Lean.mkFreshFVarId)
    let marked := target.replace fun e =>
      if isUnitInverse e then some marker else none
    let body := marked.abstract #[marker]
    let generalized := Lean.Expr.forallE `unitInv unitType body .default
    let next ← Lean.Meta.mkFreshExprMVar generalized
    goal.assign (Lean.mkApp next unitInverse)
    Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
  intro unitInv
  dsimp only [UniformizerChernNormalizationData.diagram, id] at unitInv ⊢
  -- Construct Category.assoc.symm using the category and objects of the goal.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let e := target.getAppArgs
    let a := e[1]!.getAppArgs
    let b := a[6]!.getAppArgs
    unless a[1]!.isAppOf ``CategoryTheory.Category.toCategoryStruct do
      Lean.throwError "Expected the inherited category structure"
    let cat := a[1]!.getAppArgs.back!
    let assoc := Lean.mkAppN
      (Lean.mkConst ``CategoryTheory.Category.assoc e[1]!.getAppFn.constLevels!)
      #[a[0]!, cat, a[2]!, a[3]!, b[3]!, a[4]!, a[5]!, b[5]!, b[6]!]
    let proof := Lean.mkAppN
      (Lean.mkConst ``Eq.symm target.getAppFn.constLevels!) #[e[0]!, e[2]!, e[1]!, assoc]
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal []

private theorem uniformizerAssembly
    (s : UniformizerChernNormalizationData l Y)
    (p : NormalizedAdjunctPair l Y s) :
    (s.diagram l Y).TransportTo l Y p.c
      (finiteAdjunct _ Y
        (ChernCoefficientDiagram.localAdjunctArrow l Y (s.diagram l Y) p.z)) := by
  apply coefficient_adjunct_transport l Y (s.diagram l Y) p.z p.c
  dsimp only [UniformizerChernNormalizationData.diagram]
  exact completed_adjunct_square l Y s p

/-- The prescribed comparisons transport the model adjunct to the local coefficient image.

Source: latest blueprint, diagonal tower coefficient changes proof (1), applying
coefficient functors to the section-class construction; trace proof (1), adjunction.
(blueprint: lem-diagonal-uniformizer-adjunct-transport).

Proof: completed_adjunct_square supplies the first realization square for p.c and
p.z, with its specified unit and shifted-line endpoints. For a scalar change,
scalar_unit_push identifies the coefficient-unit arrow under the defining mate.
Naturality of that mate then transports any local derived arrow, inserting and
cancelling the specified unit isomorphism on P. Apply this calculation to integral
extension and to the nonflat quotient. No positive-line endpoint normalization is
needed in this naturality argument. finite_unit_push supplies the analogous unit
square for finite realization, using the full canonical-derived-unit equation;
naturality again supplies its arbitrary-arrow version.

Compose the four arrow squares by functoriality. Naturality of q_canonical
identifies the last vertical composite with presentation.comparison. Expanding
the nested unit inverses and positive-line maps gives localUnitInv and localLine.
Finally adjunction naturality identifies the coefficient-unit arrow followed by
the pushed local class with the finite adjunct in Transported. No finite Kummer,
trace or degree identity is used. The scalar calculation does not assume flatness
or nonzero coefficients; the formulas also include n=0 and the empty scheme. -/
theorem diagonalUniformizer_adjunctTransport
    (s : UniformizerChernNormalizationData l Y)
    (p : NormalizedAdjunctPair l Y s) : p.Transported l Y s := by
  have h := uniformizerAssembly l Y s p
  rw [uniformizerLocalArrow l Y s p.z] at h
  -- The two sides differ only by the definitions of Transported and finiteAdjunct.
  -- Supply the term directly; the kernel checks this definitional conversion.
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Meta.getLocalDeclFromUserName `h
    (← Lean.Elab.Tactic.getMainGoal).assign h.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
