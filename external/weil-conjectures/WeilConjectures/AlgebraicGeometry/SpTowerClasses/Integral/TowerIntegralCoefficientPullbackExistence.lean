/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteSectionInverseImages
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteTateLineUniversal
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralInverseSystemNormalization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystemKFlat

/-! # Integral inverse image with its Kummer and flat-complex realizations

Source: blueprint classes proof (2), integral coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

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
  WeilConjectures.SemilinearSections.undoRestriction.{u + 1}
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
  unfold forgetLift_app WeilConjectures.SemilinearSections.undoRestriction finiteForgetLift
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

private def integralRingComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (Rlevel l Y n) ≅
      Rlevel l X n := by
  have := Scheme.proEtaleConstantComparison_isIso f
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  exact asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))

private theorem finite_integralInverseImages
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
        ((Rrings l Y).obj (Opposite.op n)) ((Rrings l X).obj (Opposite.op n)),
      (∀ n, (I n).modules =
        Scheme.proEtaleRingModulePullback f (Rlevel l Y n) (Rlevel l X n)
          (integralRingComparison l f n)) ∧
      (∀ n,
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
            ((sheafCompose (Scheme.ProEt.topology Y)
              (CategoryTheory.forget CommRingCat.{u + 1})).map
                ((Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) ≫
            (I n).ringUnderlying.hom =
          (I (n + 1)).ringUnderlying.hom ≫
            (sheafCompose (Scheme.ProEt.topology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).map
                ((Rrings l X).map (homOfLE (Nat.le_succ n)).op)) := by
  classical
  let c (n : ℕ) := integralRingComparison l f n
  choose theta hi hn using fun n ↦ scalarIso_exists (c n)
  let I := fun n ↦ finiteInverseImage f ((Rrings l Y).obj (Opposite.op n))
    ((Rrings l X).obj (Opposite.op n)) (c n) (theta n) (hn n)
  refine ⟨I, (fun _ ↦ rfl), ?_⟩
  intro n
  apply ringComparison_naturality f
  simpa only [c, integralRingComparison, asIso_hom, Rrings,
    Functor.ofOpSequence_map_homOfLE_succ, Rtransition] using
    Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
          (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom)))

private def powerUnitsPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).obj (powerUnits l Y) ⟶ powerUnits l X :=
  NatTrans.ofOpSequence (fun n ↦ (unitsPull f).app (Opposite.op n)) (by
    intro n
    change (upperStar AddCommGrpCat.{u + 1} f).map
        ((powerUnits l Y).map (homOfLE (Nat.le_succ n)).op) ≫ _ =
      _ ≫ (powerUnits l X).map (homOfLE (Nat.le_succ n)).op
    simp only [powerUnits, Functor.ofOpSequence_map_homOfLE_succ,
      Scheme.proEtaleUnitsPower]
    rw [Functor.map_nsmul]
    have hid := (upperStar AddCommGrpCat.{u + 1} f).map_id (Scheme.proEtaleUnitsSheaf Y)
    rw [hid]
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
    rfl)

private theorem roots_units_square {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).map
        (Scheme.proEtaleRootsOfUnityInclusion Y N) ≫
        (unitsPull f).app (Opposite.op 0) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f N ≫
        Scheme.proEtaleRootsOfUnityInclusion X N := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  dsimp only [unitsPull, Scheme.proEtaleRootsOfUnityInverseImageMap]
  change Scheme.proEtaleRootsOfUnityInclusion Y N ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
          (unitsDirect f)) =
    ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _)
      (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
        (Scheme.proEtaleRootsOfUnityDirectImageMap f N)) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change Scheme.proEtaleRootsOfUnityInclusion Y N ≫ unitsDirect f =
    Scheme.proEtaleRootsOfUnityDirectImageMap f N ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map
        (Scheme.proEtaleRootsOfUnityInclusion X N)
  ext U x
  have h := (Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap f N).exists.choose_spec U x
  change (unitsDirect f).hom.app U
      ((Scheme.proEtaleRootsOfUnityInclusion Y N).hom.app U x) =
    (Scheme.proEtaleRootsOfUnityInclusion X N).hom.app _
      ((Scheme.proEtaleRootsOfUnityDirectImageMap f N).hom.app U x)
  rw [← sections_inclusion, ← sections_inclusion]
  have hh : Scheme.proEtaleRootsOfUnitySections X N ((Scheme.proEtaleBaseChange f).op.obj U)
      ((Scheme.proEtaleRootsOfUnityDirectImageMap f N).hom.app U x) = _ := h
  apply ULift.ext
  exact congrArg (fun z ↦ Additive.ofMul (Additive.toMul z).val) hh.symm

private theorem abelian_kummer_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (cY : Chern l E Y) (cX : Chern l E X) :
    ∃ k : (abPull f).mapShortComplex.obj
        (ShortComplex.mk cY.kummer.inclusion cY.kummer.power cY.kummer.zero) ⟶
      ShortComplex.mk cX.kummer.inclusion cX.kummer.power cX.kummer.zero,
      IsIso k.τ₁ ∧
      (∀ n : ℕ, k.τ₂.app (Opposite.op n) = (unitsPull f).app (Opposite.op n)) ∧
      k.τ₃ = unitsPull f := by
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) by
      simpa only [map_natCast] using hX.map (X.Γevaluation x).hom).invertible
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (show IsUnit (l : Y.residueField y) by
      simpa only [map_natCast] using hY.map (Y.Γevaluation y).hom).invertible
  obtain ⟨r, hr⟩ := (Scheme.proEtaleRootsOfUnityInverseImageIso f).2.1 l (Fact.out : l.Prime)
  have (n : ℕᵒᵖ) : IsIso (r.app n) := by
    rw [hr n.unop]
    exact spRoots_cartesian f l (n.unop + 1)
  have : IsIso r := NatIso.isIso_of_isIso_app r
  let k : (abPull f).mapShortComplex.obj
      (ShortComplex.mk cY.kummer.inclusion cY.kummer.power cY.kummer.zero) ⟶
      ShortComplex.mk cX.kummer.inclusion cX.kummer.power cX.kummer.zero :=
    { τ₁ := r
      τ₂ := powerUnitsPull l f
      τ₃ := unitsPull f
      comm₁₂ := by
        symm
        apply NatTrans.ext
        funext n
        change (upperStar AddCommGrpCat.{u + 1} f).map
            (cY.kummer.inclusion.app n) ≫ (powerUnitsPull l f).app n =
          r.app n ≫ cX.kummer.inclusion.app n
        rw [cY.kummer.inclusion_eq n.unop, cX.kummer.inclusion_eq n.unop, hr n.unop]
        exact roots_units_square f (l ^ (n.unop + 1))
      comm₂₃ := by
        symm
        apply NatTrans.ext
        funext n
        change (upperStar AddCommGrpCat.{u + 1} f).map
            (cY.kummer.power.app n) ≫ (unitsPull f).app n =
          (powerUnitsPull l f).app n ≫ cX.kummer.power.app n
        rw [cY.kummer.power_eq n.unop, cX.kummer.power_eq n.unop]
        simp only [Scheme.proEtaleUnitsPower, Functor.map_nsmul]
        have hid := (upperStar AddCommGrpCat.{u + 1} f).map_id
          (Scheme.proEtaleUnitsSheaf Y)
        rw [hid]
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
        rfl }
  exact ⟨k, inferInstance, (fun _ ↦ rfl), rfl⟩

/-- Construct inverse image at the integral quotient stage, independently of any
ordinary or derived extension to the coefficient ring A. The middle Kummer map
is the pullback of full units, as is the last map required by the data record.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
integral reduction; Stacks `sites-cohomology`, lemma-pullback-K-flat, and
`sites-modules`, lemma-pullback-flat.
(blueprint: lem-sp-tower-integral-coefficient-pullback-existence).

Proof: realize abelian towers as sheaves on the vertical sequence site. Pull back
module sheaves with their actions by the exact geometric inverse image. The
constant-sheaf comparison for Z/ell^(n+1) is an isomorphism; its naturality in ring
maps identifies the quotient transitions. Transport the module actions along it.
Use ordinaryInverseSystem_exists on these finite inverse images to assemble
the exact whole-system functor, with its component and transition equations.
The section identities of Forget identify the underlying abelian component
comparisons, and their transition equations give the whole forgetful square.
Multiplication identifies its coefficient unit with the coefficient
unit on X. The integer generator maps to the integer generator because the
constant comparison preserves one, giving unit_normalization. Pull back the
Kummer sequence, using unitsPull for both full-units components. Restriction of
roots is its kernel map, and is invertible because roots of unity are cartesian
when ell is invertible. Transport it through rootForget on each side. Integer
multiplication commutes with restriction, so the root map is R-linear. All these
maps commute with the ell-power and quotient transitions. They give d and both
Kummer normalizations, including the displayed middle-component equation.
On the same sequence sites this is precisely pullback for the ringed-topos map
with the above constant-ring comparison. Pullback preserves flat sheaves by
lemma-pullback-flat and preserves flat-term K-flat complexes by
lemma-pullback-K-flat. Transport these properties through the identification of
module categories to obtain the displayed resolving property. The construction
uses actual inverse image, not a selected arbitrary module structure; it also
works on empty charts and for the positive level indexed by zero. -/
theorem integralCoefficientPullback_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (cY : Chern l E Y) (cX : Chern l E X) :
    ∃ d : IntegralCoefficientPullback l E f cY cX,
      (∀ n : ℕ, d.kummer.τ₂.app (Opposite.op n) =
        (unitsPull f).app (Opposite.op n)) ∧
      (∀ (P : CochainComplex (Systems Y (Rrings l Y)) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients
            (R := WeilConjectures.SemilinearSections.systemRing
              (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
                (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite
            (J := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology Y))
            (R := WeilConjectures.SemilinearSections.systemRing
              (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
                (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) (P.X i)) →
          CochainComplex.IsKFlatIndependentCoefficients
            (R := WeilConjectures.SemilinearSections.systemRing
              (Scheme.ProEt.topology X) (fun n ↦ (Rrings l X).obj (Opposite.op n))
                (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op))
            ((d.pull.mapHomologicalComplex (.up ℤ)).obj P)) := by
  classical
  let J := Scheme.ProEt.topology Y
  let J' := Scheme.ProEt.topology X
  let B := fun n ↦ (Rrings l Y).obj (Opposite.op n)
  let τ := fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op
  let F := fun n ↦ (Rrings l X).obj (Opposite.op n)
  let σ := fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op
  let uInv := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let : PreservesFiniteLimits uInv :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  obtain ⟨I, hmodules, hI⟩ := finite_integralInverseImages l f
  let (n : ℕ) : PreservesFiniteLimits (I n).modules :=
    WeilConjectures.SemilinearSections.algebraicInverse_limits.{u + 1, u, u + 1} J J' uInv _ _ (I n)
  let (n : ℕ) : PreservesFiniteColimits (I n).modules := by
    rw [hmodules n]
    let : PreservesColimitsOfSize.{0, 0}
        (Scheme.proEtaleRingModulePullback f (Rlevel l Y n) (Rlevel l X n)
          (integralRingComparison l f n)) :=
      (Scheme.proEtaleRingModuleAdjunction f (Rlevel l Y n) (Rlevel l X n)
        (integralRingComparison l f n)).leftAdjoint_preservesColimits
    infer_instance
  let (n : ℕ) : (I n).modules.Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨P⟩ := WeilConjectures.SemilinearSections.ordinaryInverseSystem_exists.{u + 1, u, u + 1}
    J B τ J' uInv F σ I hI
  let : P.pull.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨e, i, hi⟩ := integralInverseSystem_normalization l f I P
    cY.reduction.forget cX.reduction.forget
  obtain ⟨k, hk, hk₂, hk₃⟩ := abelian_kummer_pullback l E f hX hY cY cX
  let : IsIso k.τ₁ := hk
  let a : cX.reduction.forget.F.obj (P.pull.obj cY.rootModule) ≅
      cX.reduction.forget.F.obj cX.rootModule :=
    (e.app cY.rootModule).symm ≪≫ (abPull f).mapIso cY.rootForget ≪≫
      asIso k.τ₁ ≪≫ cX.rootForget.symm
  obtain ⟨r, hr⟩ := integralForgetIso l X cX.reduction.forget a
  let d : IntegralCoefficientPullback l E f cY cX :=
    { pull := P.pull
      forgetIso := e
      unitIso := i
      rootIso := r
      unit_normalization := hi
      kummer := k
      kummer_roots := by
        rw [hr]
        dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
        change k.τ₁ = (abPull f).map cY.rootForget.inv ≫
          (e.app cY.rootModule).hom ≫ (e.app cY.rootModule).inv ≫
            (abPull f).map cY.rootForget.hom ≫ k.τ₁ ≫
              cX.rootForget.inv ≫ cX.rootForget.hom
        rw [Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id,
          ← Functor.map_comp_assoc, Iso.inv_hom_id]
        rw [(abPull f).map_id, Category.id_comp]
      kummer_units := hk₃ }
  refine ⟨d, hk₂, ?_⟩
  intro K hK hf
  exact WeilConjectures.SemilinearSections.ordinaryInverseSystem_kflat.{u + 1, u, u + 1}
    J B τ J' uInv
    (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) F σ I P K hK hf

end AlgebraicGeometry.ProEtale.SpTowerClasses
