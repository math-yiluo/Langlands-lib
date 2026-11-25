/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
import WeilConjectures.CategoryTheory.TorsionSheafConstantModule
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Module.ZMod
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
/-! # Normalizing the integral coefficient-unit comparison

Source: blueprint latest, classes proof (2), integral reduction, and Stacks 03CY.
The additive comparison of constant residue towers lifts uniquely to modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime]

section Lifting

attribute [local irreducible] WeilConjectures.SemilinearSections.systemRing

-- A module over the constant residue ring has the canonical normalized scalar action.
private theorem constant_normalized (T : Scheme.{u}) (k : ℕ)
    (M : SheafOfModules.{u + 1} (constantZModRingSheaf (Scheme.ProEt.topology T) k)) :
    IsConstantZModSheafModuleStructure (Scheme.ProEt.topology T) k
      ((SheafOfModules.toSheaf _).obj M)
      (fun V ↦ (inferInstance : Module
        ((constantZModRingSheaf (Scheme.ProEt.topology T) k).obj.obj V) (M.val.obj V))) := by
  constructor
  · intro V z y
    change ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} (ZMod k))))).app V
          (z : ULift.{u + 1} (ZMod k))) • (show M.val.obj V from y) =
            z • (show M.val.obj V from y)
    rw [map_intCast, Int.cast_smul_eq_zsmul]
  · intro V W i b y
    exact M.val.map_smul i b y

-- Normalize each module action on integer sections, then use torsion-sheaf linearity.
private theorem constant_linear (T : Scheme.{u}) (k : ℕ) (hk : 0 < k)
    (M N : SheafOfModules.{u + 1} (constantZModRingSheaf (Scheme.ProEt.topology T) k))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (U : T.ProEtᵒᵖ) (a : (constantZModRingSheaf (Scheme.ProEt.topology T) k).obj.obj U)
    (x : M.val.obj U) :
    f.hom.app U (a • x) = a • (show N.val.obj U from f.hom.app U x) := by
  exact torsionSheaf_hom_linear (Scheme.ProEt.topology T) k hk
    ((SheafOfModules.toSheaf _).obj M) ((SheafOfModules.toSheaf _).obj N)
    (constantZModModuleSheaf_nsmul _ k hk M)
    (constantZModModuleSheaf_nsmul _ k hk N) f _ _
    (constant_normalized T k M) (constant_normalized T k N) U a x

-- Restriction along the coefficient comparison preserves the underlying additive sheaf.
private theorem transported_linear (T : Scheme.{u}) (k : ℕ) (hk : 0 < k)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1})
    (e : R ≅ constantZModRingSheaf (Scheme.ProEt.topology T) k)
    (M N : SheafOfModules.{u + 1} R)
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (U : T.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U) :
    f.hom.app U (a • x) = a • (show N.val.obj U from f.hom.app U x) := by
  have h := constant_linear T k hk
    ((SheafOfModules.restrictScalars e.inv).obj M)
    ((SheafOfModules.restrictScalars e.inv).obj N) f U (e.hom.hom.app U a) x
  have he : e.inv.hom.app U (e.hom.hom.app U a) = a :=
    congrArg (fun g ↦ g.hom.app U a) e.hom_inv_id
  change f.hom.app U (e.inv.hom.app U (e.hom.hom.app U a) • x) =
    e.inv.hom.app U (e.hom.hom.app U a) • (show N.val.obj U from f.hom.app U x) at h
  simpa only [he] using h

private theorem integral_sheaf_hom_linear (T : Scheme.{u}) (n : ℕ)
    (M N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (Rlevel l T n))
    (φ : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (U : T.ProEtᵒᵖ)
    (r : (WeilConjectures.SemilinearSections.ring (Scheme.ProEt.topology T)
      (Rlevel l T n)).obj.obj U) (x : M.val.obj U) :
    φ.hom.app U (r • x) = r • (show N.val.obj U from φ.hom.app U x) := by
  exact transported_linear T (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    _ (Scheme.purTwistFiniteRingIso T l n) M N φ U r x

private def towerPresheaf {T : Scheme.{u}} (A : Ab T) :
    (ℕ × T.ProEt)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
    Functor.uncurry.obj (A ⋙ sheafToPresheaf _ _)

private def forgetPresheafIso (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (M : Systems T B) :
    towerPresheaf (F.F.obj M) ≅ M.val.presheaf := by
  refine NatIso.ofComponents (fun U ↦
    eqToIso (F.sections M U.unop.1 (Opposite.op U.unop.2))) ?_
  intro U V g
  let n := V.unop.1
  let m := U.unop.1
  let W := Opposite.op U.unop.2
  let Z := Opposite.op V.unop.2
  have ht := transport_addHom (F.sections M m W) (F.sections M n W)
    ((((F.F.obj M).map g.unop.1.op).hom.app W))
    (M.val.presheaf.map (Prod.mkHom g.unop.1 (𝟙 U.unop.2)).op)
    (by
      have he : homOfLE (leOfHom g.unop.1) = g.unop.1 := Subsingleton.elim _ _
      have hf := F.transitions M (leOfHom g.unop.1) W
      rw [he] at hf
      exact hf.trans (by rfl))
  have hv := transport_addHom (F.sections M n W) (F.sections M n Z)
    (((F.F.obj M).obj (Opposite.op n)).obj.map g.unop.2.op)
    (M.val.presheaf.map (Prod.mkHom (𝟙 n) g.unop.2).op)
    (F.restrictions M n g.unop.2.op)
  change (((F.F.obj M).map g.unop.1.op).hom.app W ≫
      ((F.F.obj M).obj (Opposite.op n)).obj.map g.unop.2.op) ≫
        eqToHom (F.sections M n Z) =
    eqToHom (F.sections M m W) ≫ M.val.presheaf.map g
  rw [Category.assoc, hv, ← Category.assoc, ht, Category.assoc, ← Functor.map_comp]
  rfl

private def undoRestriction {R S : RingCat.{u + 1}} (φ : R ≅ S)
    {V W : ModuleCat.{u + 1} S}
    (f : (ModuleCat.restrictScalars φ.hom.hom).obj V ⟶
      (ModuleCat.restrictScalars φ.hom.hom).obj W) : V ⟶ W :=
  ModuleCat.ofHom {
    toFun := f
    map_add' := f.hom.map_add
    map_smul' := by
      intro a x
      have h := f.hom.map_smul (φ.inv a) x
      change f (φ.hom (φ.inv a) • x) = φ.hom (φ.inv a) • f x at h
      have hi : φ.hom (φ.inv a) = a :=
        congrArg (fun k : S ⟶ S ↦ k a) φ.inv_hom_id
      simpa only [hi, RingHom.id_apply] using h }

private abbrev forgetEval (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) (n : ℕ) :=
  WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (fun n ↦ B.obj (Opposite.op n))
    (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) n

private def LevelLinearity (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) : Prop :=
  ∀ (n : ℕ) (M N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B.obj (Opposite.op n)))
    (a : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (U : T.ProEtᵒᵖ)
    (r : (WeilConjectures.SemilinearSections.ring (Scheme.ProEt.topology T)
      (B.obj (Opposite.op n))).obj.obj U) (x : M.val.obj U),
    a.hom.app U (r • x) = r • (show N.val.obj U from a.hom.app U x)

private def finiteForgetLift (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (hl : LevelLinearity T B) (n : ℕ)
    (M N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B.obj (Opposite.op n)))
    (a : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk a.hom (hl n M N a)⟩

@[irreducible] private def forgetUnderlyingLift (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  (forgetPresheafIso T B F M).inv ≫
    Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor
      (Functor.uncurry.map (Functor.whiskerRight a (sheafToPresheaf _ _))) ≫
    (forgetPresheafIso T B F N).hom

private theorem forgetUnderlyingLift_app (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N)
    (U : (ℕ × T.ProEt)ᵒᵖ) :
    (forgetUnderlyingLift T B F a).app U =
      (forgetPresheafIso T B F M).inv.app U ≫
        (a.app (Opposite.op U.unop.1)).hom.app (Opposite.op U.unop.2) ≫
        (forgetPresheafIso T B F N).hom.app U := by
  unfold forgetUnderlyingLift
  rfl

private theorem forgetUnderlyingLift_evaluation (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N)
    (U : (ℕ × T.ProEt)ᵒᵖ) :
    ((forgetEvaluationIso T B F M U.unop.1).inv ≫
      a.app (Opposite.op U.unop.1) ≫
      (forgetEvaluationIso T B F N U.unop.1).hom).hom.app (Opposite.op U.unop.2) =
        (forgetUnderlyingLift T B F a).app U := by
  rw [forgetUnderlyingLift_app]
  rfl

@[irreducible] private def forgetLift_app (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (hl : LevelLinearity T B)
    {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N) (U : (ℕ × T.ProEt)ᵒᵖ) :
    M.val.obj U ⟶ N.val.obj U :=
  undoRestriction
    ((CategoryTheory.evaluation T.ProEtᵒᵖ RingCat).obj (Opposite.op U.unop.2) |>.mapIso
      ((sheafToPresheaf (Scheme.ProEt.topology T) RingCat).mapIso
        (eqToIso (WeilConjectures.SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (fun n ↦ B.obj (Opposite.op n))
          (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) U.unop.1).symm)))
    ((finiteForgetLift T B hl U.unop.1
      ((forgetEval T B U.unop.1).obj M) ((forgetEval T B U.unop.1).obj N)
      ((forgetEvaluationIso T B F M U.unop.1).inv ≫ a.app (Opposite.op U.unop.1) ≫
        (forgetEvaluationIso T B F N U.unop.1).hom)).val.app (Opposite.op U.unop.2))

private theorem forgetLift_app_add (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (hl : LevelLinearity T B)
    {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N) (U : (ℕ × T.ProEt)ᵒᵖ) :
    AddCommGrpCat.ofHom (forgetLift_app T B F hl a U).hom.toAddMonoidHom =
      (forgetUnderlyingLift T B F a).app U := by
  rw [← forgetUnderlyingLift_evaluation T B F a U]
  unfold forgetLift_app undoRestriction finiteForgetLift
  rfl

private theorem forgetLift_app_apply (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (hl : LevelLinearity T B)
    {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N) (U : (ℕ × T.ProEt)ᵒᵖ)
    (x : M.val.obj U) :
    forgetLift_app T B F hl a U x = (forgetUnderlyingLift T B F a).app U x :=
  ConcreteCategory.congr_hom (forgetLift_app_add T B F hl a U) x

private def forgetLift (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (hl : LevelLinearity T B)
    {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N) : M ⟶ N := by
  refine ⟨{ app := forgetLift_app T B F hl a, naturality := ?_ }⟩
  intro U V g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change forgetLift_app T B F hl a V (M.val.map g x) =
    N.val.map g (forgetLift_app T B F hl a U x)
  rw [forgetLift_app_apply, forgetLift_app_apply]
  exact ConcreteCategory.congr_hom ((forgetUnderlyingLift T B F a).naturality g) x

private theorem forgetLift_map (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) (hl : LevelLinearity T B)
    {M N : Systems T B} (a : F.F.obj M ⟶ F.F.obj N) :
    F.F.map (forgetLift T B F hl a) = a := by
  apply NatTrans.ext
  funext n
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (cancel_mono (eqToHom (F.sections N n.unop U))).1
  have h := transport_addHom (F.sections M n.unop U) (F.sections N n.unop U)
    (((F.F.map (forgetLift T B F hl a)).app n).hom.app U)
    (AddCommGrpCat.ofHom
      ((forgetLift T B F hl a).val.app (Opposite.op (n.unop, U.unop))).hom.toAddMonoidHom)
    (F.morphisms (forgetLift T B F hl a) n.unop U)
  rw [h]
  have hraw : AddCommGrpCat.ofHom
      ((forgetLift T B F hl a).val.app (Opposite.op (n.unop, U.unop))).hom.toAddMonoidHom =
      (forgetUnderlyingLift T B F a).app (Opposite.op (n.unop, U.unop)) := by
    exact forgetLift_app_add T B F hl a (Opposite.op (n.unop, U.unop))
  rw [hraw, forgetUnderlyingLift_app]
  change eqToHom (F.sections M n.unop U) ≫
    (eqToHom (F.sections M n.unop U).symm ≫ (a.app n).hom.app U ≫
      eqToHom (F.sections N n.unop U)) = _
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

private theorem forgetFaithful (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) : F.F.Faithful where
  map_injective := by
    intro M N a b h
    ext U x
    have hh := congrArg
      (fun k ↦ (((k.app (Opposite.op U.unop.1)).hom.app (Opposite.op U.unop.2)).hom)) h
    have hab := eq_of_heq
      ((F.morphisms a U.unop.1 (Opposite.op U.unop.2)).symm.trans
        ((heq_of_eq hh).trans (F.morphisms b U.unop.1 (Opposite.op U.unop.2))))
    exact DFunLike.congr_fun hab x

private theorem integralForgetIso (T : Scheme.{u}) (F : Forget T (Rrings l T))
    {M N : Systems T (Rrings l T)} (a : F.F.obj M ≅ F.F.obj N) :
    ∃ b : M ≅ N, F.F.map b.hom = a.hom := by
  let hl : LevelLinearity T (Rrings l T) := integral_sheaf_hom_linear l T
  let : F.F.Faithful := forgetFaithful T _ F
  let : F.F.Full := ⟨fun a ↦ ⟨forgetLift T _ F hl a, forgetLift_map T _ F hl a⟩⟩
  exact ⟨F.F.preimageIso a, F.F.map_preimage a.hom⟩

end Lifting

private abbrev ringAdd : CommRingCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}

private theorem ringAdd_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification ringAdd.{u} := by
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective CommRingCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1, u + 1, u + 1} _
  constructor
  intro P Q f hf
  change (Scheme.ProEt.topology T).W (Functor.whiskerRight f ringAdd.{u})
  have hi : Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) f := hf.isLocallySurjective
  apply ((Scheme.ProEt.topology T).W_iff_isLocallyBijective
    (Functor.whiskerRight f ringAdd.{u})).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology T) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology T) f x⟩

private abbrev ringAb (T : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology T) ringAdd.{u}

private theorem coefficient_vertical (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (n : ℕ) {U V : T.ProEtᵒᵖ} (g : U ⟶ V) :
    ((coefficient T B).val.map (Prod.mkHom (𝟙 n) g.unop).op).hom.toAddMonoidHom =
      (((ringAb T).obj (B.obj (op n))).obj.map g).hom := by
  change (ringAdd.map
    (((WeilConjectures.SemilinearSections.rings (Scheme.ProEt.topology T)
      (fun n ↦ B.obj (op n))
      (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)).map (𝟙 (op n))).hom.app U ≫
        (B.obj (op n)).obj.map g)).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

private theorem coefficient_horizontal (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (n : ℕ) (U : T.ProEtᵒᵖ) :
    ((coefficient T B).val.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op).hom.toAddMonoidHom =
      (((B ⋙ ringAb T).map (homOfLE (Nat.le_succ n)).op).hom.app U).hom := by
  change (ringAdd.map
    (((WeilConjectures.SemilinearSections.rings (Scheme.ProEt.topology T)
      (fun n ↦ B.obj (op n))
      (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)).map
        (homOfLE (Nat.le_succ n)).op).hom.app U ≫
      (B.obj (op n)).obj.map (𝟙 U))).hom = _
  dsimp only [WeilConjectures.SemilinearSections.rings]
  erw [Functor.ofOpSequence_map_homOfLE_succ, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

private def forgetCoefficientIso (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) : F.F.obj (coefficient T B) ≅ B ⋙ ringAb T := by
  let e (n : ℕ) : (F.F.obj (coefficient T B)).obj (op n) ≅
      (ringAb T).obj (B.obj (op n)) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents
      (fun U ↦ eqToIso (F.sections (coefficient T B) n U)) (by
        intro U V g
        exact transport_addHom (F.sections (coefficient T B) n U)
          (F.sections (coefficient T B) n V) _ _
          ((F.restrictions (coefficient T B) n g).trans
            (heq_of_eq (coefficient_vertical T B n g)))))
  let a : F.F.obj (coefficient T B) ⟶ B ⋙ ringAb T :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
      intro n
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      exact transport_addHom (F.sections (coefficient T B) (n + 1) U)
        (F.sections (coefficient T B) n U) _ _
        ((F.transitions (coefficient T B) (Nat.le_succ n) U).trans
          (heq_of_eq (coefficient_horizontal T B n U))))
  have (n : ℕᵒᵖ) : IsIso (a.app n) := by
    change IsIso (e n.unop).hom
    infer_instance
  exact NatIso.ofComponents (fun n ↦ asIso (a.app n)) (by intro _ _ g; exact a.naturality g)

private def residueMap (n : ℕ) :
    CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1 + 1)))) ⟶
      CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))) :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
      (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))

private def residueAb (T : Scheme.{u}) : Ab T :=
  Functor.ofOpSequence
    (X := fun n ↦ (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (ringAdd.{u}.obj (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))) (fun n ↦
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).map
      (ringAdd.map (residueMap l n)))

private def coefficientConstantIso (T : Scheme.{u}) (F : Forget T (Rrings l T)) :
    F.F.obj (coefficient T (Rrings l T)) ≅ residueAb l T := by
  let : (Scheme.ProEt.topology T).PreservesSheafification ringAdd.{u} :=
    ringAdd_preservesSheafification T
  let e (n : ℕ) := (constantCommuteCompose (Scheme.ProEt.topology T)
    ringAdd.{u}).app
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  let a : Rrings l T ⋙ ringAb T ⟶ residueAb l T :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
      intro n
      simpa only [e, ringAb, residueMap, Functor.comp_map, Rrings, Rtransition, residueAb,
        Functor.ofOpSequence_map_homOfLE_succ, Iso.app_hom, Functor.comp_obj,
        Functor.ofOpSequence_obj, Rlevel] using
        (constantCommuteCompose (Scheme.ProEt.topology T) ringAdd.{u}).hom.naturality
          (residueMap l n))
  have (n : ℕᵒᵖ) : IsIso (a.app n) := by
    change IsIso (e n.unop).hom
    infer_instance
  exact forgetCoefficientIso T (Rrings l T) F ≪≫
    NatIso.ofComponents (fun n ↦ asIso (a.app n)) (by intro _ _ g; exact a.naturality g)

private def abConstantMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : AddCommGrpCat.{u + 1}) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
      ((constantSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).obj A) ⟶
      (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj A :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
    (proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1} A)

private theorem abConstant_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : AddCommGrpCat.{u + 1}} (a : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f).map
        ((constantSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).map a) ≫
      abConstantMap f B =
    abConstantMap f A ≫
      (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map a := by
  let L := upperStar AddCommGrpCat.{u + 1} f
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  change L.map _ ≫ (adj.homEquiv _ _).symm _ =
    (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply ((sheafificationAdjunction (ProEt.topology Y) AddCommGrpCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (ProEt.topology Y) AddCommGrpCat.{u + 1}).homEquiv _ _)
    ((presheafToSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((proEtaleBaseChange f).op.obj U))
    ((toSheafification (ProEt.topology X) AddCommGrpCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

-- The adjunct of the constant-section map, natural in the additive coefficient group.
private def abConstantComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
        upperStar AddCommGrpCat.{u + 1} f ⟶
      constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1} where
  app A := abConstantMap f A
  naturality _ _ a := abConstant_naturality f a

private theorem abConstant_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : AddCommGrpCat.{u + 1}) : IsIso ((abConstantComparison f).app A) := by
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let adjY := constantSheafAdj (ProEt.topology Y) AddCommGrpCat.{u + 1} hT
  let adjX := constantSheafAdj (ProEt.topology X) AddCommGrpCat.{u + 1} hGT
  let adj := (adjY.comp (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u + 1} (ProEt.topology Y) (ProEt.topology X) (op T))
  have he : (abConstantComparison f).app A =
      (adj.leftAdjointUniq adjX).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)).homEquiv _ _
      ((abConstantComparison f).app A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
          (proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1} A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj AddCommGrpCat.{u + 1} hT).comp
      (sheafificationAdjunction (ProEt.topology Y) AddCommGrpCat.{u + 1})).homEquiv _ _
        (proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1} A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj AddCommGrpCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) AddCommGrpCat.{u + 1}).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) AddCommGrpCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

private def residuePullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).obj (residueAb l Y) ≅ residueAb l X := by
  let a : (abPull f).obj (residueAb l Y) ⟶ residueAb l X :=
    NatTrans.ofOpSequence
      (fun n ↦ (abConstantComparison f).app
        (ringAdd.{u}.obj (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))))
      (fun n ↦ by
        change (upperStar AddCommGrpCat.{u + 1} f).map
          ((residueAb l Y).map (homOfLE (Nat.le_succ n)).op) ≫ _ = _
        simpa only [Functor.comp_map, residueAb,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (abConstantComparison f).naturality (ringAdd.map (residueMap l n)))
  have (n : ℕᵒᵖ) : IsIso (a.app n) :=
    abConstant_isIso f _
  exact NatIso.ofComponents (fun n ↦ asIso (a.app n)) (by intro _ _ g; exact a.naturality g)

private def coefficientPullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X)) :
    (abPull f).obj (FY.F.obj (coefficient Y (Rrings l Y))) ≅
      FX.F.obj (coefficient X (Rrings l X)) :=
  (abPull f).mapIso (coefficientConstantIso l Y FY) ≪≫ residuePullIso l f ≪≫
    (coefficientConstantIso l X FX).symm

private def integerResidue (n : ℕ) :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      ringAdd.{u}.obj (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) :=
  AddCommGrpCat.ofHom
    { toFun := fun k ↦ ULift.up (k.down : ZMod (l ^ (n + 1)))
      map_zero' := by
        apply ULift.ext
        exact Int.cast_zero
      map_add' := fun _ _ ↦ by
        apply ULift.ext
        exact Int.cast_add _ _ }

private theorem constantRingAb_unit (T : Scheme.{u})
    [(Scheme.ProEt.topology T).PreservesSheafification ringAdd.{u}]
    (R : CommRingCat.{u + 1}) :
    Functor.whiskerRight
        (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj R))
        ringAdd.{u} ≫
      ((constantCommuteCompose (Scheme.ProEt.topology T)
        ringAdd.{u}).hom.app R).hom =
      toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ringAdd.obj R)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc, sheafComposeIso_inv_fac]
  change toSheafify _ _ ≫ sheafifyMap _ (𝟙 _) = _
  rw [sheafifyMap_id, Category.comp_id]
  rfl

omit [Fact l.Prime] in
private theorem integerGenerator_constant (T : Scheme.{u}) (F : Forget T (Rrings l T))
    (n : ℕ) :
    (integerGenerator T (Rrings l T) F).app (op n) ≫
        (coefficientConstantIso l T F).hom.app (op n) =
      (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).map
        (integerResidue l n) := by
  let : (Scheme.ProEt.topology T).PreservesSheafification ringAdd.{u} :=
    ringAdd_preservesSheafification T
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _
    ((residueAb l T).obj (op n)).property
  ext U k
  have hg := (integerGenerator_existsUnique T (Rrings l T) F).exists.choose_spec n U k
  have hcast := transport_element
    (F.sections (coefficient T (Rrings l T)) n U) _ _ hg
  change (eqToHom (F.sections (coefficient T (Rrings l T)) n U)) _ = _ at hcast
  change (((constantCommuteCompose (Scheme.ProEt.topology T)
      ringAdd.{u}).hom.app
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U)
      ((eqToHom (F.sections (coefficient T (Rrings l T)) n U)) _) = _
  erw [hcast]
  have hc := congrArg (fun a ↦ a.app U (ULift.up (k.down : ZMod (l ^ (n + 1)))))
    (constantRingAb_unit T (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))
  have hn := congrArg (fun a ↦ a.app U k)
    (toSheafify_naturality (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map (integerResidue l n)))
  calc
    _ = (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (ringAdd.{u}.obj (CommRingCat.of
            (ULift.{u + 1} (ZMod (l ^ (n + 1)))))))).app U
            (ULift.up (k.down : ZMod (l ^ (n + 1)))) := by
      change (((constantCommuteCompose (Scheme.ProEt.topology T) ringAdd.{u}).hom.app
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U)
          (((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))).app U)
                (k.down : ULift.{u + 1} (ZMod (l ^ (n + 1))))) = _ at hc
      rw [map_intCast] at hc
      exact hc
    _ = _ := hn

omit [Fact l.Prime] in
private theorem coefficientPullIso_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X)) :
    (abPull f).map (integerGenerator Y (Rrings l Y) FY) ≫
        (coefficientPullIso l f FY FX).hom =
      integerPull f ≫ integerGenerator X (Rrings l X) FX := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono ((coefficientConstantIso l X FX).hom.app n)).1
  change (upperStar AddCommGrpCat.{u + 1} f).map
      ((integerGenerator Y (Rrings l Y) FY).app n) ≫
      ((upperStar AddCommGrpCat.{u + 1} f).map
        ((coefficientConstantIso l Y FY).hom.app n) ≫
        (abConstantComparison f).app _ ≫
        (coefficientConstantIso l X FX).inv.app n) ≫
        (coefficientConstantIso l X FX).hom.app n =
      (abConstantComparison f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        (integerGenerator X (Rrings l X) FX).app n ≫
        (coefficientConstantIso l X FX).hom.app n
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Functor.map_comp_assoc, integerGenerator_constant, integerGenerator_constant]
  exact (abConstantComparison f).naturality (integerResidue l n.unop)

/-- Pointwise normalized comparison of constant integral sections.
Source: blueprint classes proof (2), integral reduction; the coefficient ring
comparison is constructed levelwise and checked on the integer generators.
(blueprint: lem-sp-tower-integral-unit-normalization-components).

Proof: identify each forgotten coefficient system with its tower of constant
residue groups. The canonical inverse-image comparison for constant sheaves is
an isomorphism and is natural in additive group homomorphisms. Its naturality
for the integer quotient gives the generator equation. Every additive morphism
between modules over a constant residue ring is linear (Stacks 03CY); applying
this at each level makes the recorded forgetting functor fully faithful.
Conjugate the canonical abelian comparison by the supplied e, lift the resulting
isomorphism through this fully faithful functor, and cancel e with its inverse.
The generator equation then gives the asserted equality on every section. -/
theorem integralInverseSystem_unit_normalization_components (l : ℕ) [Fact l.Prime]
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
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (e : FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F) :
    ∃ i : P.pull.obj (coefficient Y (Rrings l Y)) ≅ coefficient X (Rrings l X),
      ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
        (x : (((abPull f).obj (integers Y)).obj (op n)).obj.obj U),
        (((((abPull f).map (integerGenerator Y (Rrings l Y) FY)) ≫
          e.hom.app (coefficient Y (Rrings l Y))) ≫ FX.F.map i.hom).app (op n)).hom.app U x =
        ((integerPull f ≫ integerGenerator X (Rrings l X) FX).app (op n)).hom.app U x := by
  let b := coefficientPullIso l f FY FX
  obtain ⟨i, hi⟩ := integralForgetIso l X FX
    ((e.app (coefficient Y (Rrings l Y))).symm ≪≫ b)
  have he : e.hom.app (coefficient Y (Rrings l Y)) ≫ FX.F.map i.hom = b.hom := by
    rw [hi]
    change (e.app (coefficient Y (Rrings l Y))).hom ≫
      (e.app (coefficient Y (Rrings l Y))).inv ≫ b.hom = b.hom
    rw [Iso.hom_inv_id_assoc]
  refine ⟨i, ?_⟩
  intro n U x
  have h : ((abPull f).map (integerGenerator Y (Rrings l Y) FY) ≫
      e.hom.app (coefficient Y (Rrings l Y))) ≫ FX.F.map i.hom =
      integerPull f ≫ integerGenerator X (Rrings l X) FX := by
    rw [Category.assoc, he]
    exact coefficientPullIso_normalized l f FY FX
  exact congrArg (fun a ↦ (a.app (op n)).hom.app U x) h
end AlgebraicGeometry.ProEtale.SpTowerClasses
