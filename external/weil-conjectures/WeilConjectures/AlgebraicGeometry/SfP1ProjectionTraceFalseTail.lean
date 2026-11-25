/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceFalseFactorCancel
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.SfP1ConstantUnitPullback
import WeilConjectures.AlgebraicGeometry.SfP1MiddleExchange

/-! # False projection chart trace tail -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] properExchange._proof_1 properExchange._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] DerivedCategory.singleFunctors upperStar lowerStar
  rightDerivedLowerShriek
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local semireducible] projection
attribute [local implicit_reducible] projection projectiveLineDiagonalProjection
attribute [local semireducible] coordinateTrace trace

private theorem remove_factor
    {C : Type*} [Category C] {a b c : C}
    (e : a ⟶ b) (h : b ⟶ c) (k : c ⟶ b) (g : a ⟶ c)
    (hg : e ≫ h = g) (hk : h ≫ k = 𝟙 b) : g ≫ k = e := by
  rw [← hg, Category.assoc, hk, Category.comp_id]

attribute [local semireducible] falseProjectionChartFactor

private theorem unit_tail_paste
    {C : Type*} [Category C] {a b c d e : C}
    (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (s : d ⟶ e)
    (t : a ⟶ d) (z : a ⟶ e) (h : p ≫ q ≫ r = t) (k : t ≫ s = z) :
    p ≫ q ≫ (r ≫ s) = z := by
  calc
    _ = (p ≫ q ≫ r) ≫ s := by simp only [Category.assoc]
    _ = t ≫ s := congrArg (fun v ↦ v ≫ s) h
    _ = z := k

attribute [local semireducible] constantComparison

private theorem trace_tail_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E)
    {a₀ a₁ b₀ b₁ b₂ t u v : C} {w z p : D} {s k x : E}
    {m : s ⟶ F.obj w} {c : w ⟶ z} {ci : z ⟶ G.obj t} {e : w ⟶ G.obj t}
    {kmap : s ⟶ k} {exM : k ⟶ H.obj a₁} {exL : s ⟶ H.obj a₀}
    {α : a₀ ⟶ a₁} {π₁ : a₁ ⟶ b₁} {π₀ : a₀ ⟶ b₀} {β : b₀ ⟶ b₁}
    {d₁ : b₁ ⟶ b₂} {d₂ : b₂ ⟶ t} {τ : t ⟶ u} {cs : u ⟶ v} {eps : H.obj v ⟶ x}
    {cT : H.obj t ⟶ F.obj (G.obj t)} {cU : H.obj u ⟶ F.obj (G.obj u)}
    {unitq : G.obj u ⟶ p} {cc : F.obj p ⟶ x}
    (hc : c ≫ ci = e)
    (hm : m ≫ F.map e = kmap ≫ exM ≫ H.map (π₁ ≫ d₁ ≫ d₂) ≫ cT)
    (he : kmap ≫ exM = exL ≫ H.map α)
    (hn : α ≫ π₁ = π₀ ≫ β)
    (ht : H.map τ ≫ cU = cT ≫ F.map (G.map τ))
    (hu : cU ≫ F.map unitq ≫ cc = H.map cs ≫ eps) :
    m ≫ F.map c ≫ F.map ci ≫ F.map (G.map τ ≫ unitq) ≫ cc =
      exL ≫ H.map (π₀ ≫ β ≫ d₁ ≫ d₂ ≫ τ ≫ cs) ≫ eps := by
  rw [← F.map_comp_assoc, hc, reassoc_of% hm]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% he, ← reassoc_of% ht, hu]
  rw [← H.map_comp_assoc, hn]
  simp only [Functor.map_comp, Category.assoc]

-- Keep naturality abstract until the source object has the trace definition's native shift.
private theorem trace_tail_natural
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (G : C ⥤ D) (H : C ⥤ E)
    (R T : E ⥤ C) (η : R ≅ T) {a b : E} (j : b ≅ a)
    {b₂ t u v : C} {w z p : D} {s k x : E}
    {m : s ⟶ F.obj w} {c : w ⟶ z} {ci : z ⟶ G.obj t} {e : w ⟶ G.obj t}
    {kmap : s ⟶ k} {exM : k ⟶ H.obj (R.obj b)}
    {exL : s ⟶ H.obj (R.obj a)}
    {d₁ : T.obj b ⟶ b₂} {d₂ : b₂ ⟶ t} {g : T.obj b ⟶ t} {τ : t ⟶ u}
    {cs : u ⟶ v} {eps : H.obj v ⟶ x}
    {cT : H.obj t ⟶ F.obj (G.obj t)} {cU : H.obj u ⟶ F.obj (G.obj u)}
    {unitq : G.obj u ⟶ p} {cc : F.obj p ⟶ x}
    (hc : c ≫ ci = e)
    (hm : m ≫ F.map e = kmap ≫ exM ≫ H.map (η.hom.app b ≫ d₁ ≫ d₂) ≫ cT)
    (he : kmap ≫ exM = exL ≫ H.map (R.map j.inv))
    (ht : H.map τ ≫ cU = cT ≫ F.map (G.map τ))
    (hu : cU ≫ F.map unitq ≫ cc = H.map cs ≫ eps)
    (hg : g ≫ τ ≫ cs = d₁ ≫ d₂ ≫ τ ≫ cs) :
    m ≫ F.map c ≫ F.map ci ≫ F.map (G.map τ ≫ unitq) ≫ cc =
      exL ≫ H.map (traceComposite R T η j g τ cs) ≫ eps := by
  unfold traceComposite
  rw [hg]
  exact trace_tail_paste F G H hc hm he (η.hom.naturality j.inv) ht hu

/-- The false projection chart tail equals the transported coordinate trace.
Source: blueprint thm-amb-p1-adjunction.proof.md, first-coordinate calculation.
(auxiliary; not a blueprint node).

Proof: chart exchange and cancellation of the chart factor give projectionExchange.
The middle exchange formula separates the inverse shifted-line comparison and the
geometric exchange square. Naturality of exchange and proper forget-supports moves
that inverse comparison into the transported trace. Naturality of the pullback
compositor carries the arbitrary trace arrow through the composition comparison.
The unit composition formula and constant-unit pullback identity finish the tail.
The categorical pasting is performed for abstract functors, then specialized with
the native source shift used by the definition of trace. -/
theorem falseProjectionChartTail
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteP1DiagonalChartMap A N hA t S hS false) ≫
        (ordinaryFinitePullback A i.hom).map
          (falseProjectionChartFactorInv A N hA t S hS) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS τ false := by
  have hc : ordinaryFiniteP1DiagonalChartMap A N hA t S hS false ≫
      falseProjectionChartFactorInv A N hA t S hS =
      projectionExchange A N hA t S hS false := by
    exact remove_factor (projectionExchange A N hA t S hS false)
      (falseProjectionChartFactor A N hA t S hS)
      (falseProjectionChartFactorInv A N hA t S hS)
      (ordinaryFiniteP1DiagonalChartMap A N hA t S hS false)
      (chartExchange A N hA t S hS false)
      (falseProjectionChartFactor_cancel A N hA t S hS)
  have he :
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f false)).map
          ((ordinaryFinitePullback A (pullback.snd f f)).map
            (ordinaryFiniteShiftedLinePullback A N hA t i.hom
              (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv) ≫
        (SfDiagonalKernel.exchangeFirst A f).inv.app
          ((ordinaryFinitePullback A i.hom).obj
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) =
      (SfDiagonalKernel.exchangeFirst A f).inv.app
          ((shiftFunctor
            (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (2 : ℤ)).obj (ordinaryFiniteLine A N hA X)) ≫
        (ordinaryFinitePullback A f).map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
            (ordinaryFiniteShiftedLinePullback A N hA t i.hom
              (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv) := by
    simpa only [projection, Functor.comp_map, CoordinateTrace.pull,
      ordinaryFinitePullback] using
      (SfDiagonalKernel.exchangeFirst A f).inv.naturality
        (ordinaryFiniteShiftedLinePullback A N hA t i.hom
          (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv
  have hτ :
      (ordinaryFinitePullback A f).map τ ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          i.hom (ProjectiveLine S ↘ S) f hi.symm).hom.app (ordinaryFiniteUnit A S) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          i.hom (ProjectiveLine S ↘ S) f hi.symm).hom.app
            (ordinaryFiniteP1SplittingTarget A N hA S) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ) := by
    simpa only [Functor.comp_map, ordinaryFinitePullback] using
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.naturality τ
  have hu := ordinaryFiniteUnitPullback_comp A i.hom (ProjectiveLine S ↘ S) f hi.symm
  have hu' :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.app (ordinaryFiniteUnit A S) ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫
        (constantComparison A i).hom =
      (ordinaryFinitePullback A f).map (constantUnit A S).hom ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom := by
    exact unit_tail_paste _ _ _ _ _ _ hu (constantUnit_pullback A f)
  have h := trace_tail_natural
    (C := DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (D := DerivedCategory (Sheaf (ProjectiveLine S).smallEtaleTopology
      (ModuleCat.{u + 1} A)))
    (E := DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a := (shiftFunctor
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (2 : ℤ)).obj (ordinaryFiniteLine A N hA X))
    (ordinaryFinitePullback A i.hom)
    (ordinaryFinitePullback A (ProjectiveLine S ↘ S)) (ordinaryFinitePullback A f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (ordinaryFinitePushforward A f)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f)
    (ordinaryFiniteShiftedLinePullback A N hA t i.hom
      (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS))
    hc (middle_exchange A N hA t f i hi hS) he hτ hu'
    (presentationTrace_assoc A f i hi
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
      (τ ≫ (constantUnit A S).hom))
  simpa only [coordinateTrace, trace, CoordinateTrace.pull,
    ordinaryFinitePullback, id_eq] using h

end AlgebraicGeometry.Etale.SfP1Transport
