/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
import WeilConjectures.AlgebraicGeometry.SfP1ExchangeIsoTransport

/-! # The intermediate false projection comparison -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local irreducible] DerivedCategory.singleFunctors upperStar lowerStar
  rightDerivedLowerShriek
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local semireducible] projection
attribute [local implicit_reducible] projection projectiveLineDiagonalProjection

private theorem inverse_square
    {C : Type*} [Category C] {x y z t v : C}
    (a : x ≅ y) (b : z ≅ t) (c : t ≅ v) (d : y ≅ v) (s : x ⟶ z)
    (h : s ≫ b.hom ≫ c.hom = a.hom ≫ d.hom) :
    d.hom ≫ c.inv ≫ b.inv = a.inv ≫ s := by
  apply (cancel_mono (b.hom ≫ c.hom)).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun w ↦ a.inv ≫ w) h.symm

private theorem coefficient_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    (coefficientComparison A N hA t f i hi hS).inv ≫
        (ordinaryFinitePullback A (productMap f i hi)).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (projectiveLineDiagonalProjection S true)
            (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv =
      (ordinaryFinitePullback A (pullback.snd f f)).map
          (ordinaryFiniteShiftedLinePullback A N hA t i.hom
            (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (projectionSquare f i hi true).toCommSq).hom.app
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) := by
  let q := ProjectiveLine S ↘ S
  let v := projectiveLineDiagonalProjection S true
  let w := productMap f i hi
  let hP := finiteP1_unitOnPullback N q hS
  let hW := finiteP1_unitOnPullback N (pullback.fst q q ≫ q) hS
  let hX := finiteP1_unitOnPullback N f hS
  have he := ordinaryFiniteShiftedLinePullback_square A N hA t
    (projectionSquare f i hi true).toCommSq hP hX hW
  dsimp only [projection] at he
  unfold coefficientComparison
  simp only [Iso.trans_inv, Iso.symm_inv]
  simpa only [Category.assoc, Functor.mapIso_inv, CoordinateTrace.pull,
    ordinaryFinitePullback, q, v, w] using inverse_square
    ((ordinaryFinitePullback A (pullback.snd f f)).mapIso
      (ordinaryFiniteShiftedLinePullback A N hA t i.hom hP))
    ((ordinaryFinitePullback A w).mapIso
      (ordinaryFiniteShiftedLinePullback A N hA t v hP))
    (ordinaryFiniteShiftedLinePullback A N hA t w hW)
    (ordinaryFiniteShiftedLinePullback A N hA t (pullback.snd f f) hX) _ he

private theorem map_factor_paste
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {a b c : C} {d e : D} (l : a ⟶ c) (α : a ⟶ b) (β : b ⟶ c)
    (x : R.obj c ⟶ d) (y : d ⟶ e) (ψ : R.obj b ⟶ e)
    (hc : l = α ≫ β) (hp : R.map β ≫ x ≫ y = ψ) :
    R.map l ≫ x ≫ y = R.map α ≫ ψ := by
  rw [hc, R.map_comp]
  simpa only [Category.assoc] using congrArg (fun z ↦ R.map α ≫ z) hp

private theorem middleComposite_map
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    {F : C ⥤ D} {H : C ⥤ E} {P : E ⥤ T} (R : D ⥤ T)
    (b : F ⋙ R ≅ H ⋙ P) {W V : C} {B : D} (e : F.obj W ≅ B) (d : W ⟶ V) :
    middleComposite R b e ≫ P.map (H.map d) =
      R.map (e.inv ≫ F.map d) ≫ b.hom.app V := by
  unfold middleComposite
  rewrite [Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ R.map e.inv ≫ z) (b.hom.naturality d).symm

private theorem middleComposite_map_comp
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    {F : C ⥤ D} {H : C ⥤ E} {P : E ⥤ T} (R : D ⥤ T)
    (b : F ⋙ R ≅ H ⋙ P) {W V : C} {B : D} {K : E}
    (e : F.obj W ≅ B) (d : W ⟶ V) (h : H.obj V ⟶ K) :
    middleComposite R b e ≫ P.map (H.map d ≫ h) =
      R.map (e.inv ≫ F.map d) ≫ b.hom.app V ≫ P.map h := by
  rw [P.map_comp, ← Category.assoc, middleComposite_map, Category.assoc]

-- Paste while the functors are variables, before specializing their derived models.
private theorem middleComposite_factor
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    {F : C ⥤ D} {H : C ⥤ E} {P : E ⥤ T} (R : D ⥤ T)
    (b : F ⋙ R ≅ H ⋙ P) {W V : C} {B : D} {K : E}
    (e : F.obj W ≅ B) (d : W ⟶ V) (h : H.obj V ⟶ K)
    {Y : D} (α : B ⟶ Y) (β : Y ⟶ F.obj V)
    (ψ : R.obj Y ⟶ P.obj K)
    (hc : e.inv ≫ F.map d = α ≫ β)
    (hp : R.map β ≫ b.hom.app V ≫ P.map h = ψ) :
    middleComposite R b e ≫ P.map (H.map d ≫ h) = R.map α ≫ ψ := by
  exact (middleComposite_map_comp R b e d h).trans
    (map_factor_paste R _ α β _ _ ψ hc hp)

attribute [local semireducible] middleComparison projectionExchange

/-- The middle false comparison is the coefficient transport followed by exchange pasting.
Source: blueprint thm-amb-p1-adjunction.proof.md, first-coordinate exchange calculation.
(auxiliary; not a blueprint node).

Proof: naturality of projectionComparison carries the opposite-projection line
inverse through middleComposite. The normalized shifted-line square, with the two
line isomorphisms cancelled, identifies this transported line comparison with
pullback of the isomorphism i followed by the derived second-projection square.
Apply coefficient-independent exchangeIsoTransport to the shifted line and
associate the resulting factors. This proves precisely the displayed equation. -/
theorem middle_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (projectionExchange A N hA t S hS false) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f false)).map
          ((ordinaryFinitePullback A (pullback.snd f f)).map
            (ordinaryFiniteShiftedLinePullback A N hA t i.hom
              (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv) ≫
        (SfDiagonalKernel.exchangeFirst A f).inv.app
          ((ordinaryFinitePullback A i.hom).obj
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
        (ordinaryFinitePullback A f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom.app
              ((ordinaryFinitePullback A i.hom).obj
                ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
            (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
              (ProjectiveLine S ↘ S) f hi).inv.app
                ((ordinaryFinitePullback A i.hom).obj
                  ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
            (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
              ((pushPull A i).hom.app
                ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
          (ProjectiveLine S ↘ S) f hi.symm).hom.app
            ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
              ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) := by
  exact middleComposite_factor
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f false))
    (projectionComparison A f i hi false)
    (coefficientComparison A N hA t f i hi hS)
    (ordinaryFiniteShiftedLinePullback A N hA t
      (projectiveLineDiagonalProjection S true)
      (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv
    ((properExchange A (projectiveProjectionSquare S false)).inv.app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    _ _ _ (coefficient_square A N hA t f i hi hS)
    (exchangeIsoTransport A f i hi
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))

end AlgebraicGeometry.Etale.SfP1Transport
