/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.CategoryTheory.SectionProjectionUnit
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Exchange under a change of chart in the upper corner -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
-- `TwoSquare` is already reducible in Mathlib.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  conjugateIsoEquiv conjugateEquiv derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp derivedSquareUpperStarIso
  rightDerivedLowerStarCongr rightDerivedLowerStarComp
private theorem transport_named_pair
    {I J : Type*} {i : I} {j : J}
    (P : ∀ i' j', i' = i → j' = j → Prop) (h : P i j rfl rfl)
    {i' : I} {j' : J} (hi : i' = i) (hj : j' = j) : P i' j' hi hj := by
  subst hi
  subst hj
  exact h

/-- Abstract chart transport with its two compositors kept as explicit parameters. -/
def chartCoefficientComposite
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : D ⥤ C) (P : C ⥤ E) (Q₀ Q : D ⥤ E)
    (adj : F ⊣ R) (cmp : R ⋙ P ≅ Q₀) (eq : Q₀ ≅ Q)
    (V : C) (V' : D) (c : F.obj V ⟶ V') : P.obj V ⟶ Q.obj V' :=
  P.map (adj.unit.app V) ≫ cmp.hom.app (F.obj V) ≫
    eq.hom.app (F.obj V) ≫ Q.map c

/-- Components of abstract chart transport retain the indicated four factors. -/
theorem chartCoefficientComposite_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : D ⥤ C) (P : C ⥤ E) (Q₀ Q : D ⥤ E)
    (adj : F ⊣ R) (cmp : R ⋙ P ≅ Q₀) (eq : Q₀ ≅ Q)
    (V : C) (V' : D) (c : F.obj V ⟶ V') :
    chartCoefficientComposite F R P Q₀ Q adj cmp eq V V' c =
      P.map (adj.unit.app V) ≫ cmp.hom.app (F.obj V) ≫
        eq.hom.app (F.obj V) ≫ Q.map c := by
  rfl

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]

/-- The coefficient transport along a chart, with the derived constructions cached
before specializing the coefficient category. -/
@[irreducible]
def derivedChartCoefficientMap
    {W W' X : Scheme.{u}} (e : W' ⟶ W) (p : W ⟶ X)
    (p' : W' ⟶ X) (hp : e ≫ p = p')
    (V : DerivedCategory (Sheaf W.smallEtaleTopology B))
    (V' : DerivedCategory (Sheaf W'.smallEtaleTopology B))
    (c : (upperStar B e).leftDerivedFunctor.obj V ⟶ V') :
    (lowerStar B p).rightDerivedFunctor.obj V ⟶
      (lowerStar B p').rightDerivedFunctor.obj V' :=
  chartCoefficientComposite
    (upperStar B e).leftDerivedFunctor (lowerStar B e).rightDerivedFunctor
    (lowerStar B p).rightDerivedFunctor (lowerStar B (e ≫ p)).rightDerivedFunctor
    (lowerStar B p').rightDerivedFunctor (derivedUpperStarLowerStarAdjunction B e)
    (rightDerivedLowerStarComp B e p) (rightDerivedLowerStarCongr B hp) V V' c

/-- The component equation for chart coefficient transport. -/
theorem derivedChartCoefficientMap_eq
    {W W' X : Scheme.{u}} (e : W' ⟶ W) (p : W ⟶ X)
    (p' : W' ⟶ X) (hp : e ≫ p = p')
    (V : DerivedCategory (Sheaf W.smallEtaleTopology B))
    (V' : DerivedCategory (Sheaf W'.smallEtaleTopology B))
    (c : (upperStar B e).leftDerivedFunctor.obj V ⟶ V') :
    derivedChartCoefficientMap B e p p' hp V V' c =
      (lowerStar B p).rightDerivedFunctor.map
          ((derivedUpperStarLowerStarAdjunction B e).unit.app V) ≫
        (rightDerivedLowerStarComp B e p).hom.app
          ((upperStar B e).leftDerivedFunctor.obj V) ≫
        (rightDerivedLowerStarCongr B hp).hom.app
          ((upperStar B e).leftDerivedFunctor.obj V) ≫
        (lowerStar B p').rightDerivedFunctor.map c := by
  unfold derivedChartCoefficientMap
  exact chartCoefficientComposite_eq
    (upperStar B e).leftDerivedFunctor (lowerStar B e).rightDerivedFunctor
    (lowerStar B p).rightDerivedFunctor (lowerStar B (e ≫ p)).rightDerivedFunctor
    (lowerStar B p').rightDerivedFunctor (derivedUpperStarLowerStarAdjunction B e)
    (rightDerivedLowerStarComp B e p) (rightDerivedLowerStarCongr B hp) V V' c

/-- The square pullback comparison respects composition in its upper corner. -/
theorem derivedSquareUpperStarIso_chart
    {W W' X P Y : Scheme.{u}} {a : W ⟶ P} {p : W ⟶ X}
    {q : P ⟶ Y} {f : X ⟶ Y} (sq : CommSq a p q f) (e : W' ⟶ W)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (leftDerivedUpperStarComp B e p).hom.app
        ((upperStar B f).leftDerivedFunctor.obj K) ≫
      (upperStar B e).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso B sq).hom.app K) ≫
      (leftDerivedUpperStarComp B e a).inv.app
        ((upperStar B q).leftDerivedFunctor.obj K) =
      (derivedSquareUpperStarIso B
        (CommSq.mk (show (e ≫ a) ≫ q = (e ≫ p) ≫ f by
          simp only [Category.assoc]; rw [sq.w]))).hom.app K := by
  have h₁ := leftDerivedUpperStarComp_assoc'_app B e p f (e ≫ p) (a ≫ q)
    ((e ≫ a) ≫ q) rfl sq.w (by simpa only [Category.assoc] using congrArg (fun v ↦ e ≫ v) sq.w) K
  have h₂ := leftDerivedUpperStarComp_assoc'_app B e a q (e ≫ a) (a ≫ q)
    ((e ≫ a) ≫ q) rfl rfl rfl K
  apply (cancel_epi ((leftDerivedUpperStarComp B (e ≫ p) f ((e ≫ a) ≫ q)
    (by simpa only [Category.assoc] using congrArg (fun v ↦ e ≫ v) sq.w)).hom.app K)).mp
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₂]
  simp only [Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]

/-- Direct-image composition is the conjugate of the inverse-image compositor. -/
theorem chart_rightDerivedLowerStarComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (rightDerivedLowerStarComp B f g).hom =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction B g).comp
          (derivedUpperStarLowerStarAdjunction B f))
        (derivedUpperStarLowerStarAdjunction B (f ≫ g))
        (leftDerivedUpperStarComp B f g).hom := by
  rw [conjugateEquiv_leftDerivedUpperStarComp_hom]
  simp only [rightDerivedLowerStarComp, conjugateIsoEquiv_apply_inv,
    Iso.symm_hom, Iso.symm_inv]

/-- Inserting the chart unit and composing direct images gives exchange for the chart. -/
theorem derivedBaseChangeMap_chart
    {W W' X P Y : Scheme.{u}} {a : W ⟶ P} {p : W ⟶ X}
    {q : P ⟶ Y} {f : X ⟶ Y} (sq : CommSq a p q f) (e : W' ⟶ W)
    (M : DerivedCategory (Sheaf P.smallEtaleTopology B)) :
    (derivedBaseChangeMap B sq).app M ≫
        (lowerStar B p).rightDerivedFunctor.map
          ((derivedUpperStarLowerStarAdjunction B e).unit.app
            ((upperStar B a).leftDerivedFunctor.obj M)) ≫
        (rightDerivedLowerStarComp B e p).hom.app
          ((upperStar B e).leftDerivedFunctor.obj
            ((upperStar B a).leftDerivedFunctor.obj M)) ≫
        (lowerStar B (e ≫ p)).rightDerivedFunctor.map
          ((leftDerivedUpperStarComp B e a).inv.app M) =
      (derivedBaseChangeMap B
        (CommSq.mk (show (e ≫ a) ≫ q = (e ≫ p) ≫ f by
          simp only [Category.assoc]; rw [sq.w]))).app M := by
  rw [chart_rightDerivedLowerStarComp_hom]
  have hh := Adjunction.mate_chart_pasting
    (derivedUpperStarLowerStarAdjunction B q)
    (derivedUpperStarLowerStarAdjunction B p)
    (derivedUpperStarLowerStarAdjunction B e)
    (derivedUpperStarLowerStarAdjunction B (e ≫ p))
    (derivedSquareUpperStarIso B sq).hom (leftDerivedUpperStarComp B e p).hom M
  have hb := Adjunction.mate_bottom_naturality
    (U := (upperStar B f).leftDerivedFunctor)
    (V := (upperStar B a).leftDerivedFunctor ⋙ (upperStar B e).leftDerivedFunctor)
    (V' := (upperStar B (e ≫ a)).leftDerivedFunctor)
    (derivedUpperStarLowerStarAdjunction B q)
    (derivedUpperStarLowerStarAdjunction B (e ≫ p))
    (Functor.whiskerLeft (upperStar B f).leftDerivedFunctor
        (leftDerivedUpperStarComp B e p).hom ≫
      Functor.whiskerRight (derivedSquareUpperStarIso B sq).hom
        (upperStar B e).leftDerivedFunctor)
    (leftDerivedUpperStarComp B e a).inv M
  have hc :
      Functor.whiskerLeft (upperStar B f).leftDerivedFunctor
          (leftDerivedUpperStarComp B e p).hom ≫
        Functor.whiskerRight (derivedSquareUpperStarIso B sq).hom
          (upperStar B e).leftDerivedFunctor ≫
        Functor.whiskerLeft (upperStar B q).leftDerivedFunctor
          (leftDerivedUpperStarComp B e a).inv =
      (derivedSquareUpperStarIso B
        (CommSq.mk (show (e ≫ a) ≫ q = (e ≫ p) ≫ f by
          simp only [Category.assoc]; rw [sq.w]))).hom := by
    ext K
    exact derivedSquareUpperStarIso_chart B sq e K
  dsimp only [derivedBaseChangeMap, derivedBaseChangeSquare]
  rw [reassoc_of% hh, hb]
  rw [← Category.assoc] at hc
  rw [hc]

/-- The chart exchange identity with the actual named chart projection and top arrow. -/
theorem derivedBaseChangeMap_chart_of_eq
    {W W' X P Y : Scheme.{u}} {a : W ⟶ P} {p : W ⟶ X}
    {q : P ⟶ Y} {f : X ⟶ Y} (sq : CommSq a p q f) (e : W' ⟶ W)
    (p' : W' ⟶ X) (hp : p' = e ≫ p) (a' : W' ⟶ P) (ha : a' = e ≫ a)
    (sq' : CommSq a' p' q f) (M : DerivedCategory (Sheaf P.smallEtaleTopology B)) :
    (derivedBaseChangeMap B sq).app M ≫
        (lowerStar B p).rightDerivedFunctor.map
          ((derivedUpperStarLowerStarAdjunction B e).unit.app
            ((upperStar B a).leftDerivedFunctor.obj M)) ≫
        (rightDerivedLowerStarComp B e p).hom.app
          ((upperStar B e).leftDerivedFunctor.obj
            ((upperStar B a).leftDerivedFunctor.obj M)) ≫
        (rightDerivedLowerStarCongr B (Z := W') (Y := X)
          (g₁ := e ≫ p) (g₂ := p') hp.symm).hom.app
          ((upperStar B e).leftDerivedFunctor.obj
            ((upperStar B a).leftDerivedFunctor.obj M)) ≫
        (lowerStar B p').rightDerivedFunctor.map
          ((leftDerivedUpperStarComp B e a a' ha).inv.app M) =
      (derivedBaseChangeMap B sq').app M := by
  revert sq'
  apply transport_named_pair (i := e ≫ p) (j := e ≫ a) (hi := hp) (hj := ha)
  intro sq'
  simpa only [rightDerivedLowerStarCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] using derivedBaseChangeMap_chart B sq e M

/-- A coefficient comparison can be moved through chart exchange using its composition law. -/
theorem derivedBaseChangeMap_chart_coefficient
    {W W' X P Y : Scheme.{u}} {a : W ⟶ P} {p : W ⟶ X}
    {q : P ⟶ Y} {f : X ⟶ Y} (sq : CommSq a p q f) (e : W' ⟶ W)
    (p' : W' ⟶ X) (hp : p' = e ≫ p) (a' : W' ⟶ P) (ha : a' = e ≫ a)
    (sq' : CommSq a' p' q f) (M : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (V : DerivedCategory (Sheaf W.smallEtaleTopology B))
    (V' : DerivedCategory (Sheaf W'.smallEtaleTopology B))
    (c : (upperStar B a).leftDerivedFunctor.obj M ⟶ V)
    (c' : (upperStar B e).leftDerivedFunctor.obj V ⟶ V')
    (c'' : (upperStar B a').leftDerivedFunctor.obj M ⟶ V')
    (hc : (upperStar B e).leftDerivedFunctor.map c ≫ c' =
      (leftDerivedUpperStarComp B e a a' ha).inv.app M ≫ c'') :
    (derivedBaseChangeMap B sq).app M ≫
        (lowerStar B p).rightDerivedFunctor.map c ≫
        (lowerStar B p).rightDerivedFunctor.map
          ((derivedUpperStarLowerStarAdjunction B e).unit.app V) ≫
        (rightDerivedLowerStarComp B e p).hom.app
          ((upperStar B e).leftDerivedFunctor.obj V) ≫
        (rightDerivedLowerStarCongr B (Z := W') (Y := X)
          (g₁ := e ≫ p) (g₂ := p') hp.symm).hom.app
          ((upperStar B e).leftDerivedFunctor.obj V) ≫
        (lowerStar B p').rightDerivedFunctor.map c' =
      (derivedBaseChangeMap B sq').app M ≫
        (lowerStar B p').rightDerivedFunctor.map c'' := by
  have hu := (derivedUpperStarLowerStarAdjunction B e).unit.naturality c
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  have hn := (rightDerivedLowerStarComp B e p).hom.naturality
    ((upperStar B e).leftDerivedFunctor.map c)
  have hm := (rightDerivedLowerStarCongr B (Z := W') (Y := X)
          (g₁ := e ≫ p) (g₂ := p') hp.symm).hom.naturality
    ((upperStar B e).leftDerivedFunctor.map c)
  dsimp only [Functor.comp_map] at hn hm
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hm]
  rw [← Functor.map_comp, hc, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (lowerStar B p').rightDerivedFunctor.map c'')
    (derivedBaseChangeMap_chart_of_eq B sq e p' hp a' ha sq' M)

/-- The chart coefficient pasting formula in terms of its cached construction. -/
theorem derivedBaseChangeMap_chart_coefficient_cached
    {W W' X P Y : Scheme.{u}} {a : W ⟶ P} {p : W ⟶ X}
    {q : P ⟶ Y} {f : X ⟶ Y} (sq : CommSq a p q f) (e : W' ⟶ W)
    (p' : W' ⟶ X) (hp : p' = e ≫ p) (a' : W' ⟶ P) (ha : a' = e ≫ a)
    (sq' : CommSq a' p' q f) (M : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (V : DerivedCategory (Sheaf W.smallEtaleTopology B))
    (V' : DerivedCategory (Sheaf W'.smallEtaleTopology B))
    (c : (upperStar B a).leftDerivedFunctor.obj M ⟶ V)
    (c' : (upperStar B e).leftDerivedFunctor.obj V ⟶ V')
    (c'' : (upperStar B a').leftDerivedFunctor.obj M ⟶ V')
    (hc : (upperStar B e).leftDerivedFunctor.map c ≫ c' =
      (leftDerivedUpperStarComp B e a a' ha).inv.app M ≫ c'') :
    (derivedBaseChangeMap B sq).app M ≫
        (lowerStar B p).rightDerivedFunctor.map c ≫
        derivedChartCoefficientMap B e p p' hp.symm V V' c' =
      (derivedBaseChangeMap B sq').app M ≫
        (lowerStar B p').rightDerivedFunctor.map c'' := by
  rw [derivedChartCoefficientMap_eq]
  exact derivedBaseChangeMap_chart_coefficient B sq e p' hp a' ha sq' M V V' c c' c'' hc

end AlgebraicGeometry.Etale
