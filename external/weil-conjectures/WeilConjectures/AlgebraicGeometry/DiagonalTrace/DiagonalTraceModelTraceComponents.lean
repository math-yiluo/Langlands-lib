/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceTwistedSplittingComponents
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientProjection

/-! # Integration from unit and Chern components of the model trace

Source: diagonal tower trace proof paragraphs (1)--(2), inverse splitting and finite projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor diagonalCompletedRestriction
  SpTowerClasses.coefficient SheafOfModules.unit exactConeComparison

/-- The actual inverse-splitting trace kills the twisted unit and sends the
relative Chern adjunct to one.

Source: diagonal tower trace proof paragraph (1)
Proof: substitute the two established components of the twisted splitting and the
formula defining the model trace. The twisted pushforward isomorphism cancels its
inverse. Functoriality combines the splitting and its inverse, so they cancel as
well. The remaining two biproduct composites are inl followed by snd, which is
zero, and inr followed by snd, which is identity. The positive-unit and contraction
isomorphisms preserve these two equations. -/
private theorem model_trace_components
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (t : Result l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    t.model.twistedUnit l (ULift.{u} (Padic l)) ≫
        t.model.trace l (ULift.{u} (Padic l)) = 0 ∧
      t.model.chernAdjoint l (ULift.{u} (Padic l)) ≫
        t.model.trace l (ULift.{u} (Padic l)) = 𝟙 _ := by
  let p := t.toPresentation
  let E := ULift.{u} (Padic l)
  let T := p.twistS.T l E ⋙
    shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S)) (2 : ℤ)
  let a := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
    (2 : ℤ)).mapIso (p.twistS.positiveUnit l E).symm
  let b := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (2 : ℤ)).mapIso
        (((p.twistS.T l E).commShiftIso (-2 : ℤ)).app
          (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    (shiftFunctorCompIsoId (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (-2 : ℤ) 2 (by decide)).app
        ((p.twistS.T l E).obj (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    p.twistS.contract l E
  obtain ⟨_heval, hu, hc⟩ := diagonalTrace_twistedSplitting_components l p hS
  change p.model.twistedUnit l E =
    a.hom ≫ T.map biprod.inl ≫ T.map (p.model.bq l E) ≫
      (p.model.twistedPush l E).hom at hu
  change p.model.chernAdjoint l E =
    b.inv ≫ T.map biprod.inr ≫ T.map (p.model.bq l E) ≫
      (p.model.twistedPush l E).hom at hc
  have ht : p.model.trace l E = (p.model.twistedPush l E).inv ≫
      T.map (inv (p.model.bq l E)) ≫ T.map biprod.snd ≫ b.hom := by
    rfl
  have hunit : p.model.twistedUnit l E ≫ p.model.trace l E = 0 := by
    calc
      _ = a.hom ≫ T.map
          (biprod.inl ≫ p.model.bq l E ≫ inv (p.model.bq l E) ≫ biprod.snd) ≫
            b.hom := by
        rw [hu, ht]
        simp only [T.map_comp, Category.assoc,
          (p.model.twistedPush l E).hom_inv_id_assoc]
      _ = 0 := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inl_snd, Functor.map_zero,
          comp_zero, zero_comp]
  have hchern : p.model.chernAdjoint l E ≫ p.model.trace l E = 𝟙 _ := by
    calc
      _ = b.inv ≫ T.map
          (biprod.inr ≫ p.model.bq l E ≫ inv (p.model.bq l E) ≫ biprod.snd) ≫
            b.hom := by
        rw [hc, ht]
        simp only [T.map_comp, Category.assoc,
          (p.model.twistedPush l E).hom_inv_id_assoc]
      _ = 𝟙 _ := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inr_snd]
        rw [T.map_id]
        exact (congrArg (fun k ↦ b.inv ≫ k) (Category.id_comp b.hom)).trans
          b.inv_hom_id
  exact ⟨hunit, hchern⟩

private theorem integrate_components
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {L I K : C} {M : D}
    (u : L ⟶ K) (c : I ⟶ K) (τ : K ⟶ I)
    (hu : u ≫ τ = 0) (hc : c ≫ τ = 𝟙 I)
    (g : M ⟶ F.obj K) (π : M ⟶ F.obj I)
    (h : ∃ β : M ⟶ F.obj L, g = β ≫ F.map u + π ≫ F.map c) :
    g ≫ F.map τ = π := by
  obtain ⟨β, hβ⟩ := h
  rw [hβ, Preadditive.add_comp]
  simp only [Category.assoc, ← F.map_comp, hu, hc, F.map_zero, F.map_id,
    comp_zero, Category.comp_id, zero_add]

private theorem projection_invariance
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {I J K L M N : D}
    (g : A ⟶ B) (τ : B ⟶ A) (c : F.obj A ⟶ I) (π : I ⟶ J)
    (s : F.obj B ⟶ K) (ρ : K ⟶ L) (t : L ⟶ J)
    (j : J ⟶ M) (k : M ⟶ N) (q : F.obj A ⟶ N)
    (hred : F.map τ ≫ c ≫ π = s ≫ ρ ≫ t)
    (hpre : F.map g ≫ s ≫ ρ ≫ t = c ≫ π)
    (hcone : c ≫ π ≫ j ≫ k = q) :
    F.map (g ≫ τ) ≫ q = q := by
  rw [← hcone, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hred, reassoc_of% hpre]

private theorem normalized_projection_invariance
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory C]
    (U : A ⥤ B) (V : C ⥤ (ℕᵒᵖ ⥤ B)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M : A) (N : C)
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) (n : ℕ)
    {P : DerivedCategory A} {K : DerivedCategory (ℕᵒᵖ ⥤ B)}
    (g : (DerivedCategory.singleFunctor A 0).obj M ⟶ P)
    (τ : P ⟶ (DerivedCategory.singleFunctor A 0).obj M)
    (s : U.mapDerivedCategory.obj P ⟶ L.R.obj K)
    (r : ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.obj K ⟶
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.obj
        (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj N)))
    (hred : U.mapDerivedCategory.map τ ≫ exactConeComparison U V L M N π ≫
        (L.projection n).app _ = s ≫ (L.projection n).app K ≫ r)
    (hpre : U.mapDerivedCategory.map g ≫ s ≫ (L.projection n).app K ≫ r =
      exactConeComparison U V L M N π ≫ (L.projection n).app _) :
    U.mapDerivedCategory.map (g ≫ τ) ≫
        (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map (π.app (op n)) =
      (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map (π.app (op n)) := by
  let ev := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
  exact projection_invariance U.mapDerivedCategory g τ
    (exactConeComparison U V L M N π) ((L.projection n).app _)
    s ((L.projection n).app K) r
    (ev.map ((V.mapDerivedCategorySingleFunctor 0).hom.app N))
    ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app
      (V.obj N)) _ hred hpre
    (diagonalTrace_exactConeComparison_projection U V L M N π n)

private theorem map_tail
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B Z : C} {I J K : D} (a : I ⟶ J) (b : J ⟶ K) (c : K ⟶ F.obj A)
    (v : A ⟶ B) (τ : B ⟶ Z) (q : I ⟶ F.obj Z)
    (h : (a ≫ b ≫ c ≫ F.map v) ≫ F.map τ = q) :
    a ≫ b ≫ c ≫ F.map (v ≫ τ) = q := by
  simpa only [F.map_comp, Category.assoc] using h

private theorem projected_trace_of_components
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (t : Result l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (g : completedUnit l S ⟶ t.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧))
    (n : ℕ)
    (hcomponents :
      let E := ULift.{u} (Padic l)
      let V := t.restrictionS.F.mapDerivedCategory
      let ev := ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory
      ∃ β : (diagonalCompletedUnderlying l S).obj (completedUnit l S) ⟶
          ev.obj (V.obj ((SpTowerClasses.line l E t.chernS)⟦(2 : ℤ)⟧)),
        (diagonalCompletedUnderlying l S).map g ≫ t.toPresentation.sourceMap l E ≫
            (t.LS.projection n).app _ ≫ ev.map (t.varying.inv.app _) =
          β ≫ ev.map (V.map (t.model.twistedUnit l E)) +
            (t.coefficientsS.unitMap l E t.LS ≫ (t.LS.projection n).app _) ≫
              ev.map (V.map (t.model.chernAdjoint l E))) :
    let E := ULift.{u} (Padic l)
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory
    (diagonalCompletedUnderlying l S).map g ≫ t.toPresentation.sourceMap l E ≫
        (t.LS.projection n).app _ ≫ ev.map (t.toPresentation.systemTrace l E) =
      t.coefficientsS.unitMap l E t.LS ≫ (t.LS.projection n).app _ := by
  let E := ULift.{u} (Padic l)
  let U := diagonalCompletedUnderlying l S
  let V := t.restrictionS.F.mapDerivedCategory
  let ev := ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj
    (op n)).mapDerivedCategory
  obtain ⟨hu, hc⟩ := model_trace_components l t hS
  obtain ⟨β, hβ⟩ := hcomponents
  change U.map g ≫ t.toPresentation.sourceMap l E ≫
      (t.LS.projection n).app _ ≫ ev.map (t.varying.inv.app _) =
    β ≫ ev.map (V.map (t.model.twistedUnit l E)) +
      (t.coefficientsS.unitMap l E t.LS ≫ (t.LS.projection n).app _) ≫
        ev.map (V.map (t.model.chernAdjoint l E)) at hβ
  have hβ' := integrate_components (V ⋙ ev)
    (t.model.twistedUnit l E) (t.model.chernAdjoint l E) (t.model.trace l E)
    hu hc _ _ ⟨β, hβ⟩
  exact map_tail ev (U.map g) (t.toPresentation.sourceMap l E)
    ((t.LS.projection n).app _) (t.varying.inv.app _)
    (V.map (t.model.trace l E)) _ hβ'

/-- A source map with a base component and a coefficient-one Chern component
integrates to the canonical coefficient projection.

Source: diagonal tower trace proof paragraphs (1)--(2)
(blueprint: lem-sfb-diagonal-trace-model-trace-components).
Proof: the twisted-splitting component identities identify the unit and Chern
arrows as the two inclusions followed by the splitting. Substitute the definition
of the actual model trace and cancel the twisted-pushforward isomorphism and the
splitting against their inverses. The biproduct equations show that the unit is
killed and the Chern adjunct is sent to one.

Exact restriction and evaluation preserve these equations. Apply the evaluated
trace to the assumed pretrace sum. Additivity kills its arbitrary base term and
leaves the projected coefficient unit. Result.reductions identifies this with the
projection of the completed trace composite. Finally, the normalized exact-cone
projection theorem identifies the coefficient unit and its derived projection,
followed by the restriction/evaluation single comparisons, with the actual
ordinary coefficientProjection. Postcomposing the equality by these comparisons
gives the displayed identity. -/
theorem diagonalTrace_integral_of_components
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (t : Result l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (g : completedUnit l S ⟶ t.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧))
    (n : ℕ)
    (hcomponents :
      let E := ULift.{u} (Padic l)
      let V := t.restrictionS.F.mapDerivedCategory
      let ev := ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory
      ∃ β : (diagonalCompletedUnderlying l S).obj (completedUnit l S) ⟶
          ev.obj (V.obj ((SpTowerClasses.line l E t.chernS)⟦(2 : ℤ)⟧)),
        (diagonalCompletedUnderlying l S).map g ≫ t.toPresentation.sourceMap l E ≫
            (t.LS.projection n).app _ ≫ ev.map (t.varying.inv.app _) =
          β ≫ ev.map (V.map (t.model.twistedUnit l E)) +
            (t.coefficientsS.unitMap l E t.LS ≫ (t.LS.projection n).app _) ≫
              ev.map (V.map (t.model.chernAdjoint l E))) :
    (diagonalCompletedUnderlying l S).map (g ≫ t.trace) ≫
        ((diagonalCompletedRestriction l S).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor (DiagonalMod l S) 0).map
          (t.coefficientsS.coefficientProjection.app (op n)) =
      ((diagonalCompletedRestriction l S).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor (DiagonalMod l S) 0).map
          (t.coefficientsS.coefficientProjection.app (op n)) := by
  let E := ULift.{u} (Padic l)
  let ev := ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory
  exact normalized_projection_invariance
    (A := DiagonalCompleted l S) (B := DiagonalMod l S)
    (C := SpTowerClasses.Systems S (SpTowerClasses.Arings l E S))
    (diagonalCompletedRestriction l S) t.restrictionS.F t.LS
    (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
    (SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S))
    t.coefficientsS.coefficientProjection n g t.trace
    (t.toPresentation.sourceMap l E) (ev.map (t.toPresentation.systemTrace l E))
    (t.reductions n) (projected_trace_of_components l t hS g n hcomponents)

end AlgebraicGeometry.ProEtale.DiagonalTrace
