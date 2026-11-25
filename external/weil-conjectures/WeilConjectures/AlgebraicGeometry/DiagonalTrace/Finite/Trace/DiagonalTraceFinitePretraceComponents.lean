/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteDivisorAdjoint
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceDivisorChernAdjoint

/-! # Finite components of the supported diagonal before applying trace

Source: diagonal tower trace proof paragraph (2), and the supported diagonal
component formula in the finite projective-line adjunction.
(blueprint: lem-sfb-diagonal-trace-finite-pretrace-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- At one coefficient level, the supported diagonal has an arbitrary base component
and exactly one positive relative Chern component, before applying any trace.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (2), together with
the divisor-line, Chern-additivity and adjunction argument in
`lem-amb-p1-diagonal-chern-components`.
(blueprint: lem-sfb-diagonal-trace-finite-pretrace-components).

Proof: finite projection and the normalized supported-source comparison identify
this arrow with the projected coefficient unit followed by the evaluated Chern
adjunct of the actual diagonal divisor line (finiteDivisorAdjoint).

Factor that divisor line into a base pullback and the hyperplane line of p.model.
Chern additivity, normalized Chern pullback and naturality of the geometric
adjunction give the two tower components (divisorChernAdjoint_components).
Pulling hY back gives the invertibility hypotheses of that tower identity.

Apply the additive exact restriction and evaluation functors to the identity,
and precompose with the projected coefficient unit. Its base component is the
witness beta; its relative component has coefficient one. This calculation uses
no trace, inverse splitting or integration identity. -/
theorem diagonalTrace_finitePretrace_components
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let V := p.restrictionS.F.mapDerivedCategory
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    ∃ β : (diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
        (completedUnit l (ProjectiveLine Y)) ⟶
      ev.obj (V.obj ((SpTowerClasses.line l E p.chernS)⟦(2 : ℤ)⟧)),
      (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
          (a.hom ≫ p.Rc.R.map δ) ≫ p.sourceMap l E ≫
          (p.LS.projection n).app _ ≫ ev.map (p.varying.inv.app _) =
        β ≫ ev.map (V.map (p.model.twistedUnit l E)) +
          (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
            ev.map (V.map (p.model.chernAdjoint l E)) := by
  let E := ULift.{u} (Padic l)
  let V := p.restrictionS.F.mapDerivedCategory
  let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
    (op n)).mapDerivedCategory
  let q := p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _
  have hS : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hX : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  obtain ⟨β, hβ⟩ := diagonalTrace_divisorChernAdjoint_components l E Y hS hX f hf p
  refine ⟨q ≫ ev.map (V.map β), ?_⟩
  rw [diagonalTrace_finiteDivisorAdjoint l Y hY D δ hδ f p a n, hβ]
  simp only [q, ev, V, E, Functor.map_add, Functor.map_comp,
    Preadditive.comp_add, Category.assoc]

end AlgebraicGeometry.ProEtale.DiagonalTrace
