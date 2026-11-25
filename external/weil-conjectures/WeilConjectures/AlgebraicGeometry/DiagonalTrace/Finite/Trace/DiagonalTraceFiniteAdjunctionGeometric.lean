/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePushUnit

/-! # Geometric-arrow half of the finite adjunction factorization

This module calculates the geometric component of the explicitly constructed
finite direct-image operation, using its coefficient-unit component and naturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

private theorem adjunct_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {G : B ⥤ A} (adj : L ⊣ G)
    (FX : B ⥤ C) (FS : A ⥤ D) (R : C ⥤ D)
    (e : FX ⋙ R ≅ G ⋙ FS) {I : A} {J N : B} {K : C} {H : D}
    (c : L.obj I ⟶ J) (μ : H ⟶ R.obj K)
    (qx : K ⟶ FX.obj J) (qs : H ⟶ FS.obj I)
    (hu : μ ≫ R.map qx ≫ e.hom.app J = qs ≫ FS.map (adj.homEquiv I J c))
    (θ : J ⟶ N) :
    μ ≫ R.map (qx ≫ FX.map θ) ≫ e.hom.app N =
      qs ≫ FS.map (adj.homEquiv I N (c ≫ θ)) := by
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  have hn := e.hom.naturality θ
  dsimp only [Functor.comp_map] at hn
  calc
    μ ≫ R.map qx ≫ R.map (FX.map θ) ≫ e.hom.app N =
        (μ ≫ R.map qx ≫ e.hom.app J) ≫ FS.map (G.map θ) := by
      rw [hn]
      simp only [Category.assoc]
    _ = (qs ≫ FS.map (adj.homEquiv I J c)) ≫ FS.map (G.map θ) := by rw [hu]
    _ = _ := by
      rw [Category.assoc, ← FS.map_comp, adj.homEquiv_naturality_right]

/-- The actual finite direct-image operation has the geometric adjunction equation.

The previous arbitrary-function interface was false: its values on supported
classes do not determine it on all geometric classes. The source uses the
operation induced by direct image, which is the explicit operation below.

Source: geometric classes proof (3), forgetting support, together with the
coefficient-system derived comparison and exact-cone projection.
(blueprint: lem-sfb-diagonal-trace-finite-adjunction-geometric).

Proof: expand the operation as the actual coefficient unit, direct image of the
input arrow, and the finite evaluation comparison. Naturality of that comparison
moves theta to the right. The coefficient-unit seed equation identifies the
remaining prefix. Naturality of the adjunction hom-equivalence combines the
coefficient pullback and theta into the required adjunct. -/
theorem diagonalTrace_finiteAdjunction_geometric
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (n : ℕ) :
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
    ∀ θ : SpTowerClasses.unit (diagonalSurface Y)
          (SpTowerClasses.Arings l E (diagonalSurface Y)) ⟶ line,
        Φ ((p.coefficientsX.unitMap l E p.LX ≫ (p.LX.projection n).app _) ≫
          evX.map (VX.map θ)) =
          (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
            evS.map (VS.map
              ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
                ((p.model.coefficientPullback.derivedIso l E).hom ≫ θ))) := by
  dsimp only
  intro θ
  exact adjunct_naturality (SpTowerShriek.adjunction l _ p.base p.model.geometry)
    (p.restrictionX.F.mapDerivedCategory ⋙
      ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj (op n)).mapDerivedCategory)
    (p.restrictionS.F.mapDerivedCategory ⋙
      ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj (op n)).mapDerivedCategory)
    p.Rf.R (p.finitePushComparison l n) (p.model.coefficientPullback.derivedIso l _).hom
    (p.finitePushUnit l) _ _ (diagonalTrace_finitePush_unit l p n) θ

end AlgebraicGeometry.ProEtale.DiagonalTrace
