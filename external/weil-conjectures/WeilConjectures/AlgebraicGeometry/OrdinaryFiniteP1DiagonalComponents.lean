/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback

/-! # The Chern-component formula for the supported diagonal boundary

Canonical constructions: (auxiliary; not a blueprint node).

Source: blueprint lemma-class-diagonal-projective-line, standard-chart Cartier calculation;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Use the same braiding projection as the generic symmetric coefficient API.
attribute [local instance 100000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] genericConstantIso

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3

attribute [local irreducible] Scheme.finiteEtaleTateLine Scheme.kummerδ₁
  AlgebraicGeometry.ProjectiveSpace
  HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
  ordinaryFiniteIntegralGenerator ordinaryFiniteRootMap Sheaf.H.map
  Scheme.Pic.toCohomologicalPicardGroup Scheme.Pic.map ordinaryFiniteClassCore
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward

/-- The ordinary supported Ext group, with its category structures recorded once.
Source: the supported Cartier Kummer class in Stacks 03PL and 0A45.
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteSupportedExt (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} A) i).obj
    (ordinaryFiniteConstant A D)) F 2

/-- The existing supported realization, on the named ordinary degree-zero objects.
Source: supportedExactDerivedMap for the exact direct image of a closed immersion.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteSupportedRealization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) ⟶
      (ordinaryFiniteDegreeZero A T F)⟦(2 : ℤ)⟧ :=
  supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A D) F κ

/-- The supported arrow after forgetting support, on the named ordinary objects.
Source: the supported exact realization and canonical constant unit, Stacks 0A45.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteSupportedArrow (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFiniteDegreeZero A T F)⟦(2 : ℤ)⟧ :=
  supportedDerivedUnit A i ≫ ordinaryFiniteSupportedRealization A i F κ

attribute [local semireducible] ordinaryFiniteSupportedArrow

/-- Factoring the two mapped supported arrows preserves their original composite.
Source: functoriality of direct image and associativity of composition.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteSupportedArrow_pushforward (A : Type (u + 1)) [CommRing A]
    {D T U : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (p : T ⟶ U)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : ordinaryFiniteSupportedExt A i F) :
    (supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (supportedDerivedUnit A i)) ≫
          (ordinaryFinitePushforward A p).map (ordinaryFiniteSupportedRealization A i F κ) =
      supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (ordinaryFiniteSupportedArrow A i F κ) := by
  exact (Category.assoc (supportedDerivedUnit A p)
    ((ordinaryFinitePushforward A p).map (supportedDerivedUnit A i))
    ((ordinaryFinitePushforward A p).map
      (ordinaryFiniteSupportedRealization A i F κ))).trans
    (congrArg (fun f ↦ supportedDerivedUnit A p ≫ f)
      ((ordinaryFinitePushforward A p).map_comp (supportedDerivedUnit A i)
        (ordinaryFiniteSupportedRealization A i F κ)).symm)

/-- The shifted-twist direct image for one of the product projections.
Source: blueprint finite diagonal check, canonical projection direct image.
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteP1DiagonalTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool) :
    DerivedCategoryModule A (ProjectiveLine S) :=
  (ordinaryFinitePushforward A
    (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
    (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)

/-- Apply the projected supported class to the canonical constant-object unit.
This is the canonical composite before the trace in the finite diagonal integral.
Source: blueprint finite diagonal check, supported class and composition unit.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1DiagonalSupportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA)) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶ ordinaryFiniteP1DiagonalTarget A N hA S a :=
  projectiveLineDiagonalAlpha A S a ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (ordinaryFiniteSupportedRealization A (pullback.diagonal (ProjectiveLine S ↘ S))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)

/-- The canonical adjunction transport around a commuting composition diagram.
Source: adjunction-unit pasting in the projective-line diagonal calculation.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteChartTransport (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    (ordinaryFinitePushforward A p).obj L ⟶ (ordinaryFinitePushforward A r).obj L' :=
  (ordinaryFinitePushforward A p).map ((ordinaryFiniteAdjunction A e).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p).hom.app
      ((ordinaryFinitePullback A e).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) hr).hom.app
      ((ordinaryFinitePullback A e).obj L) ≫
    (ordinaryFinitePushforward A r).map v

/-- Direct-image transport from either product projection to the standard P1 projection.
This is the comparison preceding the trace in arbitraryBaseFiniteP1DiagonalTrace.
Source: blueprint lemma-class-diagonal-projective-line, identification of each projection.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  ordinaryFiniteChartTransport A e.hom p
    (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
    (projectiveLineDiagonalChart S a).property L _
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom

private theorem base_adjunct_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X L : C} {Y M : D} (e : F.obj X ≅ Y) (β : X ⟶ L)
    (v : F.obj L ⟶ M) :
    (adj.unit.app X ≫ G.map e.hom) ≫ G.map (e.inv ≫ F.map β ≫ v) =
      β ≫ adj.unit.app L ≫ G.map v := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ G.map v) (adj.unit_naturality β)

private theorem unit_chern_core {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y L : D} (e : F.obj X ⟶ Y) (d : Y ⟶ L) :
    (adj.unit.app X ≫ G.map e) ≫ G.map d = adj.homEquiv X L (e ≫ d) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

private theorem chart_adjunct_core {B C D : Type*} [Category B] [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (R : C ⥤ B) (R' : D ⥤ B) (rc : G ⋙ R ≅ R')
    {X : B} {Y L : C} {Z M : D} (e : F.obj Y ≅ Z)
    (α : X ⟶ R.obj Y) (α' : X ⟶ R'.obj Z)
    (hcomp : α ≫ R.map (adj.unit.app Y ≫ G.map e.hom) ≫ rc.hom.app Z = α')
    (d : Y ⟶ L) (v : F.obj L ⟶ M) :
    α ≫ R.map d ≫ R.map (adj.unit.app L) ≫ rc.hom.app (F.obj L) ≫ R'.map v =
      α' ≫ R'.map (e.inv ≫ F.map d ≫ v) := by
  rw [← hcomp]
  symm
  simp only [Functor.map_comp, Category.assoc]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc (G.map e.hom) (G.map e.inv), ← G.map_comp,
    Iso.hom_inv_id, G.map_id, R.map_id, Category.id_comp]
  rw [← rc.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← R.map_comp_assoc, adj.unit_naturality, R.map_comp]
  simp only [Category.assoc]

private theorem map_sum_components {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {T : D} {U V : C} (α : T ⟶ F.obj U) (δ b c : U ⟶ V)
    (b' c' : T ⟶ F.obj V) (hsum : δ = b + c)
    (hb : α ≫ F.map b = b') (hc : α ≫ F.map c = c') :
    α ≫ F.map δ = b' + c' := by
  rw [hsum, Functor.map_add, Preadditive.comp_add, hb, hc]

private theorem coefficient_chart_adjunct (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : e ≫ p = r) (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (d : ordinaryFiniteUnit A Y ⟶ L)
    (v : (ordinaryFinitePullback A e).obj L ⟶ L') :
    supportedDerivedUnit A p ≫ (ordinaryFinitePushforward A p).map d ≫
        ordinaryFiniteChartTransport A e p r hr L L' v =
      supportedDerivedUnit A r ≫ (ordinaryFinitePushforward A r).map
        (ordinaryFiniteArrowPullback A e L L' d v) := by
  unfold ordinaryFiniteChartTransport ordinaryFiniteArrowPullback
  subst r
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  exact chart_adjunct_core (ordinaryFiniteAdjunction A e)
    (ordinaryFinitePushforward A p) (ordinaryFinitePushforward A (e ≫ p))
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p)
    (ordinaryFiniteUnitPullback A e) _ _
    (by
      have hc := supportedDerivedUnit_comp A e p
      rw [supportedDerivedUnit_eq A e] at hc
      exact hc) d v

attribute [local semireducible] ordinaryFiniteSupportedRealization
  supportedKummerChern ordinaryFiniteP1KummerClass
  ordinaryFiniteLinePullbackMap ordinaryFiniteP1DiagonalChartMap
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward ordinaryFiniteP1DiagonalSupportedMap

/-- The diagonal component formula with the base hyperplane Chern arrow specified.
Source: blueprint lemma-class-diagonal-projective-line, Chern additivity and adjunct steps.
(blueprint: lem-amb-p1-diagonal-chern-fixed-base)

Proof: the supported Chern equation identifies the unsupported diagonal class with
its divisor line. The chart Picard identity factors this line into the relative
hyperplane and the pullback of the base hyperplane. Chern additivity and pullback
naturality give their sum. The chart adjunction pasting transports the supported
map to its adjunct; unit naturality sends the base summand to its Chern arrow
followed by the twisted unit, while the relative summand is the Chern pushforward.
-/
theorem ordinaryFiniteP1_diagonal_kummer_component_formula_fixed (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)))
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S) hPP c)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA))
    (hκ : SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S))
      hI hW κ) :
    ∀ a : Bool,
            ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
              ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
            ordinaryFiniteFirstChern A N hA (ProjectiveLine S) hP
                (Scheme.Pic.ofIsInvertible
                  (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)) ≫
              ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP +
              ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) c := by
  classical
  let P := ProjectiveLine S
  let β : ordinaryFiniteUnit A P ⟶ (ordinaryFiniteLine A N hA P)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteFirstChern A N hA P hP
      (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1))
  intro a
  let Q := ProjectiveLine P
  let W := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  let i : P ⟶ W := pullback.diagonal (ProjectiveLine S ↘ S)
  let r : Q ⟶ P := ProjectiveLine P ↘ P
  let d : ordinaryFiniteUnit A W ⟶
      (ordinaryFiniteLine A N hA W)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteSupportedArrow A i (Scheme.finiteEtaleTateLine W N A hA) κ
  let e : Q ⟶ W := (projectiveLineDiagonalChart S a).val.hom
  let δ : ordinaryFiniteUnit A Q ⟶
      (ordinaryFiniteLine A N hA Q)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteLinePullbackMap A N hA t e hW d
  let b : ordinaryFiniteUnit A Q ⟶
      (ordinaryFiniteLine A N hA Q)⟦(2 : ℤ)⟧ :=
    ordinaryFiniteLinePullbackMap A N hA t r hP β
  let := hI.isInvertible_dual_toModules
  have hdeq : d = ordinaryFiniteFirstChern A N hA W hW
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules)) := by
    exact ordinaryFiniteFirstChern_unique A N hA W hW
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules)) _
      (ordinary_supported_kummer_chern W N hN A hA hW i hI κ hκ)
  have hδ : δ = ordinaryFiniteFirstChern A N hA Q hPP
      (Scheme.Pic.map e (Scheme.Pic.ofIsInvertible
        (Scheme.Modules.dual i.ker.toModules))) := by
    exact (congrArg
      (ordinaryFiniteLinePullbackMap A N hA t e hW) hdeq).trans
      (ordinaryFiniteFirstChern_pullback A N hA t e hW hPP _)
  have hb : b = ordinaryFiniteFirstChern A N hA Q hPP
      (Scheme.Pic.map r (Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1))) := by
    exact ordinaryFiniteFirstChern_pullback A N hA t r hP hPP _
  have hceq : c = ordinaryFiniteFirstChern A N hA Q hPP
      (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) P 1)) := by
    exact ordinaryFiniteFirstChern_unique A N hA Q hPP _ c hc
  have hsum : δ = b + c := by
    have hp := congrArg (ordinaryFiniteFirstChern A N hA Q hPP)
      (finiteP1_diagonal_picard S hI a)
    have hm := ordinaryFiniteFirstChern_mul A N hA Q hPP
      (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) P 1))
      (Scheme.Pic.map r (Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)))
    exact hδ.trans (hp.trans (hm.trans ((add_comm _ _).trans
      (congrArg₂ (fun x y : ordinaryFiniteUnit A Q ⟶
        (ordinaryFiniteLine A N hA Q)⟦(2 : ℤ)⟧ ↦ x + y) hb.symm hceq.symm))))
  have hfactor : ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
      ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
      supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map d ≫
          ordinaryFiniteP1DiagonalChartMap A N hA t S hS a := by
    rw [ordinaryFiniteP1DiagonalSupportedMap, projectiveLineDiagonalAlpha_units]
    exact (congrArg (fun f ↦ f ≫ ordinaryFiniteP1DiagonalChartMap A N hA t S hS a)
      (ordinaryFiniteSupportedArrow_pushforward A
        (pullback.diagonal (ProjectiveLine S ↘ S))
        (projectiveLineDiagonalProjection S a) (Scheme.finiteEtaleTateLine W N A hA) κ)).trans
      (Category.assoc (supportedDerivedUnit A (projectiveLineDiagonalProjection S a))
        ((ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map d)
        (ordinaryFiniteP1DiagonalChartMap A N hA t S hS a))
  have hchart : supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map d ≫
          ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
      supportedDerivedUnit A r ≫ (ordinaryFinitePushforward A r).map δ := by
    dsimp only [ordinaryFiniteP1DiagonalChartMap, δ, ordinaryFiniteLinePullbackMap]
    exact coefficient_chart_adjunct A e
      (projectiveLineDiagonalProjection S a) r
      (projectiveLineDiagonalChart S a).property _ _ d
      (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom
  exact hfactor.trans (hchart.trans
    (map_sum_components (ordinaryFinitePushforward A r) (supportedDerivedUnit A r)
      δ b c (β ≫ ordinaryFiniteP1Unit A N hA t P hP)
      (ordinaryFiniteP1ChernPushforward A N hA P c) hsum
      (by
        rw [supportedDerivedUnit_eq A r]
        dsimp only [b, ordinaryFiniteLinePullbackMap]
        rw [ordinaryFiniteP1Unit_eq]
        unfold ordinaryFiniteArrowPullback
        exact base_adjunct_core (ordinaryFiniteAdjunction A r)
          (ordinaryFiniteUnitPullback A r) β
          (ordinaryFiniteShiftedLinePullback A N hA t r hP).hom)
      (by
        rw [supportedDerivedUnit_eq A r]
        rw [ordinaryFiniteP1ChernPushforward_eq]
        exact unit_chern_core (ordinaryFiniteAdjunction A r)
          (ordinaryFiniteUnitPullback A r).hom c)))

/-- The supported diagonal boundary has the base and relative hyperplane components.
Source: blueprint lemma-class-diagonal-projective-line, standard-chart proof;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula)

Proof: the diagonal's regular equations on the four product charts are y-x, x-y,
1-xy and xy-1. On the chart indexed by i,j the ideal generator is
(x0*y1-x1*y0)/(xi*yj). Its changes of basis identify the ideal dual with
p1*O(1) tensor p2*O(1), with the diagonal polynomial as its canonical section.
The given supported boundary, composed with the constant unit, is the Chern class
of this dual ideal, by ordinary_supported_kummer and uniqueness of its boundary.
Additivity of the Kummer connecting map on the Picard group gives the sum of the
two pulled-back hyperplane classes. Under the chart for projection a, one is the
relative O(1) class and the other is pulled back from the base P. Module-derived
Hom from the constant free rank-one sheaf is abelian cohomology evaluated at one:
resolve the target by injective module sheaves, forget to section-acyclic abelian
sheaves, and evaluate Hom on the constant generator. This is ordinaryFiniteClass
itself, so the Chern specification identifies the actual relative module-derived
arrow with c. Take beta to be the base O(1) class realized by that same comparison.
Taking adjuncts turns its pullback into beta followed by the twisted unit, and
turns the relative class into the stated Chern pushforward. The adjunction unit
pasting is exactly alpha; the composition and twist comparisons are exactly those
in ordinaryFiniteP1DiagonalChartMap. Thus their sum is the displayed formula.
The argument is over arbitrary rings, including the zero ring, and N=1 gives
the zero-coefficient arrows. No general derived-map detection by stalks is used. -/
theorem ordinaryFiniteP1_diagonal_kummer_component_formula (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)))
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S) hPP c)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : ordinaryFiniteSupportedExt A (pullback.diagonal (ProjectiveLine S ↘ S))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA))
    (hκ : SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S))
      hI hW κ) :
    ∀ a : Bool, ∃ β : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
              (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
            ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
              ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
            β ≫ ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP +
              ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) c := by
  intro a
  exact ⟨_, ordinaryFiniteP1_diagonal_kummer_component_formula_fixed N hN A hA
    t S hS hP hPP hW c hc hI κ hκ a⟩

end AlgebraicGeometry.Etale
