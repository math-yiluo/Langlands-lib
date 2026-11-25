/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceDiagonalPic
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerChernPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineBundleClassAdditive
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The two components of the diagonal divisor Chern adjunct

Source: diagonal Chern components, the Picard tensor law, and Chern pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

attribute [local irreducible] Functor.mapDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] lineBundleEtaleClass lineBundleClass firstChernR firstChern

private theorem firstChernR_mul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (L M : T.Pic) :
    firstChernR l E c (L * M) = firstChernR l E c L + firstChernR l E c M := by
  have := c.reduction.derivedAdjunction.left_adjoint_additive
  simp only [firstChernR, tower_lineBundleClass_mul, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

private theorem firstChern_mul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (L M : T.Pic) :
    firstChern l E c (L * M) = firstChern l E c L + firstChern l E c M := by
  have := c.scalar.adjunction.left_adjoint_additive
  simp only [firstChern, firstChernR_mul, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- Before any finite projection or completed limit, the Chern adjunct of the diagonal
line has a base component and the specified relative hyperplane component.

Source: lem-amb-p1-diagonal-chern-components, the divisor-line calculation and
additivity of Kummer; lem-sp-tower-chern-pullback.
(blueprint: lem-sfb-diagonal-trace-divisor-chern-adjoint).

Proof: factor the diagonal Picard class as a pullback of a base line times the
relative hyperplane line of p.model. The first Chern construction is additive:
the Picard-to-H1 map is additive, and every exact comparison, coefficient
extension and endpoint composition preserves the sum. Apply Chern pullback to
the base line with p.model's normalized coefficient and root comparisons.
It identifies that summand with pullback of its base Chern arrow followed by
the shifted line-pullback comparison. Take adjuncts. Naturality of the adjunction
unit makes this base summand the base Chern arrow followed by twistedUnit.
The relative summand is chernAdjoint by its definition. No inverse splitting,
trace, or completed diagonal arrow enters this argument. -/
theorem diagonalTrace_divisorChernAdjoint_components
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hS : IsUnit (l : Γ(ProjectiveLine Y, ⊤)))
    (hX : IsUnit (l : Γ(diagonalSurface Y, ⊤)))
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (p : Presentation l E f) :
    ∃ β : unit (ProjectiveLine Y) (Arings l E (ProjectiveLine Y)) ⟶
        (line l E p.chernS)⟦(2 : ℤ)⟧,
      (SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
          ((p.model.coefficientPullback.derivedIso l E).hom ≫
            firstChern l E p.chernX (diagonalPic Y)) =
        β ≫ p.model.twistedUnit l E + p.model.chernAdjoint l E := by
  obtain ⟨L, hL, hPic⟩ := diagonalTrace_diagonalPic_factorization Y f hf
    p.model.model p.model.over_eq
  let := hL
  let P : D (ProjectiveLine Y) (Arings l E (ProjectiveLine Y)) ⥤
      D (diagonalSurface Y) (Arings l E (diagonalSurface Y)) :=
    SpTowerShriek.pull l E p.base p.model.geometry
  let adj := SpTowerShriek.adjunction l E p.base p.model.geometry
  let β := firstChern l E p.chernS (Scheme.Pic.ofIsInvertible L)
  let θ := (P.commShiftIso (2 : ℤ)).hom.app (line l E p.chernS) ≫
    ((p.model.linePullback.derivedIso l E).hom)⟦(2 : ℤ)⟧'
  have hpull := tower_firstChern_pullback l E f hX hS p.base p.model.geometry
    p.chernS p.chernX p.normalizedS p.normalizedX
    p.model.coefficientPullback p.model.linePullback L
  have hclass : (p.model.coefficientPullback.derivedIso l E).hom ≫
      firstChern l E p.chernX (diagonalPic Y) =
    P.map β ≫ θ + (p.model.coefficientPullback.derivedIso l E).hom ≫
      firstChern l E p.chernX
        (Scheme.Pic.mapHom p.model.model.hom (hyperplanePic (ProjectiveLine Y))) := by
    rw [hPic, firstChern_mul, Preadditive.comp_add, ← hpull]
    simp only [β, θ, P]
    rfl
  have hbase : adj.homEquiv _ _ (P.map β ≫ θ) =
      β ≫ p.model.twistedUnit l E := by
    calc
      _ = β ≫ adj.homEquiv _ _ θ := adj.homEquiv_naturality_left β θ
      _ = _ := by
        rw [Adjunction.homEquiv_unit]
        rfl
  refine ⟨β, ?_⟩
  rw [hclass, Adjunction.homAddEquiv_add]
  exact congrArg (fun k ↦ k + p.model.chernAdjoint l E) hbase

end AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
