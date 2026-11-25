/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierChern
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCanonicalSupported
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteAdjunctionGeometric

/-! # Finite direct-image factorization through the unadjointed surface arrow

Source: diagonal tower trace proof (2), the direct-image/limit comparison and
composition along the diagonal; geometric classes proof (3), forgetting support.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource completedSupportedUnit

/-- The two normalized direct-image constructions factor through the same operation
on finite, unadjointed arrows on the surface. This concerns every supported arrow
and every geometric arrow, without identifying either arrow as a Cartier or Chern class.

Source: diagonal tower trace proof (2), direct-image/limit compatibility;
diagonal-limit (1), evaluation of derived direct image; geometric classes (3),
constant-to-supported unit.
(blueprint: lem-sfb-diagonal-trace-finite-adjunction-factorization).

Proof: let W be the diagonal surface and P the projective line. Evaluation of strict
constant-scalar towers commutes with derived direct image: its left adjoint is exact,
so evaluation preserves K-injectives and a common resolution gives the comparison with
p.Rf. Normalize this comparison by the ordinary identity on sections. For a map
from the restricted completed coefficient unit on W to the finite line, define
Phi by the derived direct image of that map, preceded by the ordinary coefficient
unit for f, and followed by the inverse evaluation/direct-image comparison and
the inverse varying comparison. This construction applies to every map in the
indicated Hom set, whether or not it comes from a completed or strict-system map.

For a supported arrow gamma, naturality of the completed exact square moves gamma
past p.completed. Its common-unit normalization identifies the single-object map
of a.iso with the direct image of the constant-to-support map. Indeed a.normalization
is precisely the ordinary composition comparison for diagonal followed by f, and
a.over_eq makes that composition the identity. The unit equation therefore fixes
this map with no scalar factor. The common-derived-unit equation for p.limits
identifies its projection with the evaluation/direct-image comparison used in Phi.
Naturality of the root cone then gives the first equation for every gamma.

For a geometric arrow theta, expand its adjunct as the adjunction unit followed by
the direct image of coefficientPullback.derivedIso.hom followed by theta. The
ordinary coefficient pullback normalization sends one to one. Together with
p.varying_normalization this identifies its restricted unit with the coefficient
unit used in Phi. The ordinary coefficient cone has actual quotient projections;
the exact-cone projection identity identifies the input with coefficientsS.unitMap
followed by LS.projection. Naturality gives the second equation for every theta.
No equality of arbitrary derived arrows is inferred from their finite values.
The construction uses no inverses of coefficient projections, so also covers n=0
and the empty surface. -/
theorem diagonalTrace_finiteAdjunction_factorization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
    let VX := p.restrictionX.F.mapDerivedCategory
    let VS := p.restrictionS.F.mapDerivedCategory
    let evX := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    let line := (SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧
    ∃ Φ : (UX.obj (completedUnit l (diagonalSurface Y)) ⟶ evX.obj (VX.obj line)) →
        ((diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
          (completedUnit l (ProjectiveLine Y)) ⟶
            evS.obj (VS.obj ((SpTowerShriek.push l E p.base p.model.geometry).obj line))),
      (∀ γ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y,
        Φ (UX.map
            ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
              (completedSupportedUnit l Y) ≫ γ) ≫
          shiftedComparison UX (VX ⋙ p.LX.R) (p.coefficientsX.lineMap l E p.LX) 2 ≫
            (p.LX.projection n).app _) =
          (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
              (a.hom ≫ p.Rc.R.map γ) ≫ p.sourceMap l E ≫
            (p.LS.projection n).app _ ≫ evS.map (p.varying.inv.app _)) ∧
      (∀ θ : SpTowerClasses.unit (diagonalSurface Y)
          (SpTowerClasses.Arings l E (diagonalSurface Y)) ⟶ line,
        Φ ((p.coefficientsX.unitMap l E p.LX ≫ (p.LX.projection n).app _) ≫
          evX.map (VX.map θ)) =
          (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
            evS.map (VS.map
              ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
                ((p.model.coefficientPullback.derivedIso l E).hom ≫ θ)))) := by
  let E := ULift.{u} (Padic l)
  let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
  let VX := p.restrictionX.F.mapDerivedCategory
  let VS := p.restrictionS.F.mapDerivedCategory
  let evX := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
    (op n)).mapDerivedCategory
  let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
    (op n)).mapDerivedCategory
  let line := (SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧
  let Φ := fun η : UX.obj (completedUnit l (diagonalSurface Y)) ⟶
      evX.obj (VX.obj line) ↦
    p.finitePushUnit l ≫ p.Rf.R.map η ≫ (p.finitePushComparison l n).hom.app line
  refine ⟨Φ, ?_, ?_⟩
  · intro γ
    exact diagonalTrace_finiteCanonical_supported l Y f p a n γ
  · exact diagonalTrace_finiteAdjunction_geometric l Y f p n

end AlgebraicGeometry.ProEtale.DiagonalTrace
