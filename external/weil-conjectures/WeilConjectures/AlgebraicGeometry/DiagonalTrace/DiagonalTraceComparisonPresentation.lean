/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonPartial
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonLimitIsos

/-! # Construction of the comparison data for the projective-line trace

Source: blueprint latest, diagonal-tower trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

/-- Construct the normalized geometric, scalar-restriction and limit comparisons,
without asserting the splitting or choosing a completed trace.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), and
`sk-prop-diagonal-tower/_section.md`, passage to the limit.
(blueprint: lem-sfb-diagonal-trace-comparison-presentation).

Proof: reduce the integral Kummer extension simultaneously over the quotient tower.
Its quotient and root identifications give normalized Chern data on S and X.
The compatible-root pro-etale cover trivializes the root line, so tensoring by it
has internal Hom as inverse, with the usual evaluation and coevaluation. Transport
projective-line inverse image and its adjunction along the specified model m.
The line projection mate is invertible: cancel the line and its dual in the two
adjunction Hom bijections. These constructions supply the Model fields.
Restrict each coefficient level by the residue map from Z_l, retaining sections,
restrictions and transitions. The coefficient and root projections give the two
Coefficients records; for Q_l the scalar-extension coefficient is the quotient
Z_l/l^(n+1), so these are the actual completed coefficient and root cones.
Choose total right derived direct images and total derived limits by K-injective
resolutions. The ordinary restriction/direct-image squares are identity on sections.
Derive these squares using the common-unit comparison; its K-injective computation
is the varying_normalization equation. Derive limit.post to obtain the limit square.
The ordinary limits of the two coefficient cones are their completed sheaves by
their defining projections. Quotient transitions are epimorphic, and root transitions
are epimorphic because l is invertible. The Milnor comparison therefore makes the
unit_limit and line_limit maps invertible. All geometric data were transported
along m, so the resulting model is m itself. This construction does not use any
splitting or completed trace morphism. -/
theorem exists_diagonalTraceComparisonPresentation
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (m : X ≅ ProjectiveLine S)
    (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃ p : Presentation l (ULift.{u} (Padic l)) f, p.model.model = m := by
  obtain ⟨q, hq⟩ := exists_diagonalTraceComparisonPartial l f m hm hS
  obtain ⟨hu, hl⟩ := diagonalTraceComparisonLimitIsos l f m hm hS q
  let p : Presentation l (ULift.{u} (Padic l)) f :=
    { base := q.base
      chernS := q.chernS
      chernX := q.chernX
      normalizedS := q.normalizedS
      normalizedX := q.normalizedX
      finiteS := q.finiteS
      finiteX := q.finiteX
      twistS := q.twistS
      twistX := q.twistX
      model := q.model
      restrictionS := q.restrictionS
      restrictionX := q.restrictionX
      coefficientsS := q.coefficientsS
      coefficientsX := q.coefficientsX
      LS := q.LS
      LX := q.LX
      Rf := q.Rf
      Rt := q.Rt
      Rc := q.Rc
      varyingOrdinary := q.varyingOrdinary
      varying_sections := q.varying_sections
      varying := q.varying
      varying_normalization := q.varying_normalization
      completedOrdinary := q.completedOrdinary
      completed_sections := q.completed_sections
      completed := q.completed
      limits := q.limits
      unit_limit := hu
      line_limit := hl }
  exact ⟨p, hq⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
