/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Abelian comparison for integral ordinary inverse systems

Source: blueprint classes proof (2), integral reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

open Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

private abbrev abSets (T : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})

private abbrev levelModules (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

private abbrev levelForget (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    levelModules T R ⥤ DiagonalAb T :=
  SheafOfModules.toSheaf.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

private def additionSets {T : Scheme.{u}} (A : DiagonalAb T) :
    (abSets T).obj A ⊗ (abSets T).obj A ⟶ (abSets T).obj A :=
  ⟨{ app := fun U ↦ ↾(fun z ↦ @Add.add (A.obj.obj U) inferInstance z.1 z.2)
     naturality := by
       intro U V g
       ext z
       exact ((A.obj.map g).hom.map_add _ _).symm }⟩

private def abSetComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar AddCommGrpCat.{u + 1} f ⋙ abSets X ≅
      abSets Y ⋙ Scheme.proEtaleSheafInverseImage f (Type (u + 1)) :=
  letI : RepresentablyFlat (Scheme.proEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits _
  letI : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{u + 1})

private theorem moduleAbelianComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) R S)
    (M : levelModules Y R) :
    ∃ e : (upperStar AddCommGrpCat.{u + 1} f).obj ((SheafOfModules.toSheaf _).obj M) ≅
        (SheafOfModules.toSheaf _).obj (I.modules.obj M),
      (abSets X).map e.hom = (abSetComparison f).hom.app _ ≫
        I.moduleUnderlying.inv.app M := by
  let A := (SheafOfModules.toSheaf _).obj M
  let N := (SheafOfModules.toSheaf _).obj (I.modules.obj M)
  let L := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let η := (Scheme.proEtaleSheafAdjunction f (Type (u + 1))).unit
  let β := η.app ((abSets Y).obj A) ≫
    (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).map
      (I.moduleUnderlying.inv.app M)
  have hn (Z : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
      (a : Z ⟶ (abSets Y).obj A) (U : Y.ProEtᵒᵖ) (x : Z.obj.obj U) :
      (L.map a).hom.app ((Scheme.proEtaleBaseChange f).op.obj U)
          ((η.app Z).hom.app U x) =
        (η.app ((abSets Y).obj A)).hom.app U (a.hom.app U x) := by
    exact (congrArg (fun k ↦ k.hom.app U x) (η.naturality a)).symm
  have hadd (U : Y.ProEtᵒᵖ) (x y : A.obj.obj U) :
      β.hom.app U (x + y) =
        (show N.obj.obj ((Scheme.proEtaleBaseChange f).op.obj U) from β.hom.app U x) +
          (show N.obj.obj ((Scheme.proEtaleBaseChange f).op.obj U) from β.hom.app U y) := by
    let Z := (abSets Y).obj A ⊗ (abSets Y).obj A
    have h := I.moduleAdd M Z (fst _ _) (snd _ _) (additionSets A)
      (fun _ _ ↦ rfl) ((Scheme.proEtaleBaseChange f).op.obj U)
      ((η.app Z).hom.app U (x, y))
    dsimp only [id_eq] at h
    erw [hn, hn, hn] at h
    exact h
  let b : A ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj N :=
    ⟨{ app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (β.hom.app U) (hadd U))
       naturality := by
         intro U V g
         apply AddCommGrpCat.hom_ext
         apply AddMonoidHom.ext
         intro x
         exact congrArg (fun k ↦ k x) (β.hom.naturality g) }⟩
  let a := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv A N).symm b
  have ha : (abSets X).map a = (abSetComparison f).hom.app A ≫
      I.moduleUnderlying.inv.app M := by
    let : RepresentablyFlat (Scheme.proEtaleBaseChange f) :=
      flat_of_preservesFiniteLimits _
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let c := abSetComparison f
    have hc := sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) (Scheme.proEtaleBaseChange f)
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) A
    change (abSets Y).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A) ≫
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).map (c.hom.app A) =
        η.app ((abSets Y).obj A) at hc
    have hi : η.app ((abSets Y).obj A) ≫
        (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).map (c.inv.app A) =
        (abSets Y).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A) := by
      erw [← hc, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
    apply (cancel_epi (c.inv.app A)).mp
    rw [Iso.inv_hom_id_app_assoc]
    apply ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv
      ((abSets Y).obj A) ((abSets X).obj N)).injective
    change η.app _ ≫
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).map
        (c.inv.app A ≫ (abSets X).map a) = β
    rw [Functor.map_comp, ← Category.assoc, hi]
    change (abSets Y).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv A N a) = β
    rw [Equiv.apply_symm_apply]
    rfl
  have : IsIso ((abSets X).map a) := by rw [ha]; infer_instance
  have : IsIso a := isIso_of_reflects_iso a (abSets X)
  exact ⟨asIso a, ha⟩

private abbrev levelEval (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) (n : ℕ) :
    Systems T B ⥤ levelModules T (B.obj (op n)) :=
  WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (fun n ↦ B.obj (op n))
    (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) n

private theorem transportAddHom {A B A' B' : AddCommGrpCat.{u + 1}}
    (eA : A = A') (eB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f.hom g.hom) :
    f ≫ eqToHom eB = eqToHom eA ≫ g := by
  subst A'
  subst B'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact AddCommGrpCat.hom_ext (eq_of_heq h)

attribute [local irreducible] WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  WeilConjectures.SemilinearSections.coefficientMap

private def forgetLevelObj (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (M : Systems T B) (n : ℕ) :
    (F.F.obj M).obj (op n) ≅
      (levelForget T (B.obj (op n))).obj ((levelEval T B n).obj M) := by
  refine ObjectProperty.isoMk _ ?_
  change ((F.F.obj M).obj (op n)).obj ≅ (Prod.sectR n T.ProEt).op ⋙ M.val.presheaf
  refine NatIso.ofComponents (fun U ↦ eqToIso (F.sections M n U)) ?_
  intro U V g
  exact transportAddHom (F.sections M n U) (F.sections M n V) _
    (((Prod.sectR n T.ProEt).op ⋙ M.val.presheaf).map g) (F.restrictions M n g)

private def forgetLevel (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (n : ℕ) :
    F.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalAb T)).obj (op n) ≅
      levelEval T B n ⋙ levelForget T (B.obj (op n)) := by
  refine NatIso.ofComponents (fun M ↦ forgetLevelObj T B F M n) ?_
  intro M N g
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact transportAddHom (F.sections M n U) (F.sections N n U) _ _
    (F.morphisms g n U)

private def levelTransition (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    {m n : ℕ} (h : n ≤ m) (M : Systems T B) :
    (levelForget T (B.obj (op m))).obj ((levelEval T B m).obj M) ⟶
      (levelForget T (B.obj (op n))).obj ((levelEval T B n).obj M) :=
  (SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (B.obj (op m)))).map
    ((WeilConjectures.SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (fun n ↦ B.obj (op n))
      (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) h).app M)

private theorem forgetLevel_transition (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {m n : ℕ} (h : n ≤ m) (M : Systems T B) :
    (F.F.obj M).map (homOfLE h).op ≫ (forgetLevel T B F n).hom.app M =
      (forgetLevel T B F m).hom.app M ≫ levelTransition T B h M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply transportAddHom (F.sections M m U) (F.sections M n U)
  have ht := (WeilConjectures.SemilinearSections.transition_exists.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (fun n ↦ B.obj (op n))
    (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) h).exists.choose_spec M U
  have hf := F.transitions M h U
  apply HEq.trans hf
  apply HEq.symm
  -- The transition formula is an equality of functions; it determines the additive maps.
  apply heq_of_eq
  apply AddMonoidHom.ext
  intro x
  exact congrFun (eq_of_heq ht) x

private def moduleAbIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) R S)
    (M : levelModules Y R) :=
  (moduleAbelianComparison f I M).choose

private theorem moduleAbIso_sets {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) R S)
    (M : levelModules Y R) :
    (abSets X).map (moduleAbIso f I M).hom = (abSetComparison f).hom.app _ ≫
      I.moduleUnderlying.inv.app M :=
  (moduleAbelianComparison f I M).choose_spec

private def moduleAbFunctorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))) R S) :
    SheafOfModules.toSheaf _ ⋙ upperStar AddCommGrpCat.{u + 1} f ≅
      I.modules ⋙ SheafOfModules.toSheaf _ := by
  refine NatIso.ofComponents (moduleAbIso f I) ?_
  intro M N g
  apply (abSets X).map_injective
  simp only [Functor.map_comp, moduleAbIso_sets]
  simp only [Functor.comp_map]
  erw [(abSetComparison f).hom.naturality_assoc]
  have hn := I.moduleUnderlying.inv.naturality g
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn]
  rfl

private abbrev ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (BY : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (BX : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (BY.obj (op n)) (BX.obj (op n))) :=
  WeilConjectures.SemilinearSections.OrdinaryInverseSystem.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y) (fun n ↦ BY.obj (op n))
    (fun n ↦ BY.map (homOfLE (Nat.le_succ n)).op)
    (Scheme.ProEt.topology X) (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (fun n ↦ BX.obj (op n)) (fun n ↦ BX.map (homOfLE (Nat.le_succ n)).op) I

section Ordinary

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    (BY : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (BX : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})

private def ordinaryLevel
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (BY.obj (op n)) (BX.obj (op n)))
    (P : ordinaryPull f BY BX I) (n : ℕ) :
    levelEval Y BY n ⋙ levelForget Y (BY.obj (op n)) ⋙ upperStar AddCommGrpCat.{u + 1} f ≅
      P.pull ⋙ levelEval X BX n ⋙ levelForget X (BX.obj (op n)) :=
  Functor.isoWhiskerLeft (levelEval Y BY n) (moduleAbFunctorIso f (I n)) ≪≫
    Functor.isoWhiskerRight (P.component n).symm (levelForget X (BX.obj (op n)))

private theorem ordinaryLevel_sets
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (BY.obj (op n)) (BX.obj (op n)))
    (P : ordinaryPull f BY BX I) (n : ℕ) (M : Systems Y BY) :
    (abSets X).map ((ordinaryLevel f BY BX I P n).hom.app M) ≫
        (WeilConjectures.SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (BX.obj (op n))).map ((P.component n).hom.app M) ≫
        (I n).moduleUnderlying.hom.app ((levelEval Y BY n).obj M) =
      (abSetComparison f).hom.app
        ((SheafOfModules.toSheaf _).obj ((levelEval Y BY n).obj M)) := by
  change (abSets X).map ((moduleAbIso f (I n) _).hom ≫
    (SheafOfModules.toSheaf _).map ((P.component n).inv.app M)) ≫ _ = _
  rw [Functor.map_comp, moduleAbIso_sets]
  let V := levelForget X (BX.obj (op n)) ⋙ abSets X
  change ((abSetComparison f).hom.app _ ≫ (I n).moduleUnderlying.inv.app _) ≫
    V.map ((P.component n).inv.app M) ≫
      V.map ((P.component n).hom.app M) ≫ (I n).moduleUnderlying.hom.app _ = _
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, Category.comp_id]

private theorem ordinaryLevel_transition
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (BY.obj (op n)) (BX.obj (op n)))
    (P : ordinaryPull f BY BX I) {m n : ℕ} (h : n ≤ m) (M : Systems Y BY) :
    (upperStar AddCommGrpCat.{u + 1} f).map (levelTransition Y BY h M) ≫
        (ordinaryLevel f BY BX I P n).hom.app M =
      (ordinaryLevel f BY BX I P m).hom.app M ≫
        levelTransition X BX h (P.pull.obj M) := by
  apply (abSets X).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  -- Cancel the normalized target component comparison.
  apply (cancel_mono
    ((WeilConjectures.SemilinearSections.underlying.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (BX.obj (op n))).map ((P.component n).hom.app M) ≫
      (I n).moduleUnderlying.hom.app ((levelEval Y BY n).obj M))).mp
  rw [Category.assoc, ordinaryLevel_sets]
  have hc := (abSetComparison f).hom.naturality (levelTransition Y BY h M)
  simp only [Functor.comp_map] at hc
  rw [hc]
  have ht := congrArg
    (fun k ↦ (WeilConjectures.SemilinearSections.underlying.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (BX.obj (op m))).map k ≫
        (I n).moduleUnderlying.hom.app ((levelEval Y BY n).obj M)) (P.transition h M)
  simp only [Functor.map_comp, Category.assoc] at ht
  rw [P.restriction_underlying] at ht
  have hn := (I m).moduleUnderlying.hom.naturality
    ((WeilConjectures.SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (fun n ↦ BY.obj (op n))
      (fun n ↦ BY.map (homOfLE (Nat.le_succ n)).op) h).app M)
  simp only [Functor.comp_map] at hn
  simp only [WeilConjectures.SemilinearSections.underlying, Functor.comp_map] at ht
  have ht' := ht.trans (congrArg
    (fun k ↦ (WeilConjectures.SemilinearSections.underlying.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (BX.obj (op m))).map
        ((P.component m).hom.app M) ≫ k) hn)
  have hs := congrArg
    (fun k ↦ (abSets X).map ((ordinaryLevel f BY BX I P m).hom.app M) ≫ k) ht'
  have hm := congrArg
    (fun k ↦ k ≫ (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
      ((abSets Y).map (levelTransition Y BY h M)))
    (ordinaryLevel_sets f BY BX I P m M)
  simp only [Category.assoc] at hs hm ⊢
  exact hm.symm.trans hs.symm

private theorem ordinaryAbelianComparison
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (BY.obj (op n)) (BX.obj (op n)))
    (P : ordinaryPull f BY BX I)
    (FY : Forget Y BY) (FX : Forget X BX) :
    Nonempty (FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F) := by
  let e (n : ℕ) :
      FY.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalAb Y)).obj (op n) ⋙
          upperStar AddCommGrpCat.{u + 1} f ≅
        P.pull ⋙ FX.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalAb X)).obj (op n) :=
    Functor.isoWhiskerRight (forgetLevel Y BY FY n)
        (upperStar AddCommGrpCat.{u + 1} f) ≪≫
      ordinaryLevel f BY BX I P n ≪≫
      Functor.isoWhiskerLeft P.pull (forgetLevel X BX FX n).symm
  refine ⟨NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun n ↦ (e n.unop).app M) ?_) ?_⟩
  · intro m n g
    have h : n.unop ≤ m.unop := leOfHom g.unop
    have hg : g = (homOfLE h).op := Subsingleton.elim _ _
    subst g
    change (upperStar AddCommGrpCat.{u + 1} f).map
        ((FY.F.obj M).map (homOfLE h).op) ≫ (e n.unop).hom.app M =
      (e m.unop).hom.app M ≫ (FX.F.obj (P.pull.obj M)).map (homOfLE h).op
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
    apply (cancel_mono ((forgetLevel X BX FX n.unop).hom.app (P.pull.obj M))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [forgetLevel_transition]
    simp only [← Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id, Category.comp_id]
    rw [← Functor.map_comp, forgetLevel_transition, Functor.map_comp]
    rw [Category.assoc, ordinaryLevel_transition]
    simp only [Category.assoc]
  · intro M N g
    apply NatTrans.ext
    funext n
    exact (e n.unop).hom.naturality g

end Ordinary

attribute [local irreducible] Rrings

/-- The underlying abelian tower comparison supplied by an ordinary inverse system.
Source: blueprint latest, classes proof (2), integral reduction, and Zheng Construction 4.1.
(blueprint: lem-sp-tower-integral-abelian-comparison).

Proof: at each coefficient level, the moduleUnderlying comparison of the algebraic
inverse image is composed with the component comparison of the ordinary system and
with the evaluation identifications supplied by the two Forget structures.  The
module graph equations make these maps additive.  Naturality in system morphisms
and the restriction_underlying and transition equations make the level maps
compatible with horizontal arrows, so the component maps assemble to the required
natural isomorphism of abelian towers.
-/
theorem integralInverseSystem_abelian_comparison (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      ((Rrings l Y).obj (Opposite.op n)) ((Rrings l X).obj (Opposite.op n)))
    (P : WeilConjectures.SemilinearSections.OrdinaryInverseSystem.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
      (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)
      (Scheme.ProEt.topology X) (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (fun n ↦ (Rrings l X).obj (Opposite.op n))
      (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op) I)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X)) :
    Nonempty (FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F) := by
  exact ordinaryAbelianComparison f (Rrings l Y) (Rrings l X) I P FY FX

end AlgebraicGeometry.ProEtale.SpTowerClasses
