/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Exact finite residue restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a b v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses WeilConjectures

private def constantModuleFunctor {C : Type a} [Category.{v} C]
    (R : Type b) [Ring R]
    (M : PresheafOfModules.{b} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) :
    Cᵒᵖ ⥤ ModuleCat.{b} R where
  obj := M.obj
  map f := ModuleCat.ofHom
    { toFun := M.map f
      map_add' := map_add _
      map_smul' := fun r x ↦ M.map_smul f r x }
  map_id U := by ext x; exact congrArg (fun f ↦ f x) (M.map_id U)
  map_comp f g := by ext x; exact M.map_comp_apply f g x

private def constantModuleMap {C : Type a} [Category.{v} C]
    (R : Type b) [Ring R]
    {M N : PresheafOfModules.{b} ((Functor.const Cᵒᵖ).obj (RingCat.of R))}
    (f : M ⟶ N) : constantModuleFunctor R M ⟶ constantModuleFunctor R N where
  app := f.app
  naturality U V g := by ext x; exact PresheafOfModules.naturality_apply f g x

variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

private abbrev E := ULift.{u} (Padic l)
private abbrev J := Scheme.ProEt.topology T
private abbrev Λ := ULift.{u + 1} ℤ_[l]
private abbrev A := Arings l (E l) T
private abbrev B (n : ℕ) := (A l T).obj (op n)
private abbrev τ (n : ℕ) := (A l T).map (homOfLE (Nat.le_succ n)).op
private abbrev P := SemilinearSections.ringPresheaf.{u + 1, u, u + 1}
  (J T) (B l T) (τ l T)

attribute [local instance 20000] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

private def residue (n : ℕ) : Scheme.purTwistZlConstant T l ⟶ B l T n :=
  Scheme.purTwistZlReduction T l n ≫ SpTowerClasses.coefficientMap l (E l) T n

private theorem residue_step (n : ℕ) :
    residue l T (n + 1) ≫ τ l T n = residue l T n := by
  have hc : SpTowerClasses.coefficientMap l (E l) T (n + 1) ≫ τ l T n =
      (Rrings l T).map (homOfLE (Nat.le_succ n)).op ≫
        SpTowerClasses.coefficientMap l (E l) T n := by
    simpa only [τ, A, Arings, SpTowerShriek.tau] using
      (coefficientMap_transition l (E l) T n)
  dsimp only [residue]
  rw [Category.assoc, hc, ← Category.assoc]
  congr 1
  have h := (Scheme.purTwistZlCompletionMap_existsUnique T l).exists.choose_spec
  rw [← h (n + 1), ← h n, Category.assoc]
  exact congrArg (fun f ↦ Scheme.purTwistZlCompletionMap T l ≫ f)
    (limit.w (Scheme.purTwistZlTower T l) (homOfLE (Nat.le_succ n)).op)

private def scalarCone :
    (Functor.const ℕᵒᵖ).obj (Scheme.purTwistZlConstant T l) ⟶
      SemilinearSections.rings (J T) (B l T) (τ l T) :=
  NatTrans.ofOpSequence (residue l T) (fun n ↦ by
    simp only [Functor.const_obj_map, SemilinearSections.rings,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.id_comp _).trans (residue_step l T n).symm)

private def scalarUnit :
    (Functor.const (ℕ × T.ProEt)ᵒᵖ).obj (CommRingCat.of (Λ l)) ⟶
      (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙ Functor.uncurry.obj
        ((Functor.const ℕᵒᵖ).obj ((Scheme.purTwistZlConstant T l).obj)) where
  app U := (toSheafify (J T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (Λ l)))).app (op U.unop.2)
  naturality U V f := by
    change 𝟙 _ ≫ _ = _ ≫ (𝟙 _ ≫
      (Scheme.purTwistZlConstant T l).obj.map f.unop.2.op)
    rw [Category.id_comp]
    exact (Category.id_comp _).symm.trans
      ((toSheafify (J T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (Λ l)))).naturality f.unop.2.op)

@[irreducible] private def scalarMap :
    (Functor.const (ℕ × T.ProEt)ᵒᵖ).obj (RingCat.of (Λ l)) ⟶
      P l T ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight
    (scalarUnit l T ≫ Functor.whiskerLeft
      (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor
      (Functor.uncurry.map (Functor.whiskerRight (scalarCone l T)
        (sheafToPresheaf (J T) CommRingCat.{u + 1}))))
    (forget₂ CommRingCat RingCat)

private abbrev restricted (M : Systems T (A l T)) :=
  (PresheafOfModules.restrictScalars (scalarMap l T)).obj M.val

private def fixed (M : Systems T (A l T)) :
    (ℕ × T.ProEt)ᵒᵖ ⥤ ModuleCat.{u + 1} (Λ l) :=
  constantModuleFunctor (Λ l) (restricted l T M)

private def level (M : Systems T (A l T)) (n : ℕ) : DiagonalMod l T :=
  ⟨(Prod.sectR n T.ProEt).op ⋙ fixed l T M,
    Presheaf.isSheaf_of_isSheaf_comp (J T) _
      (forget₂ (ModuleCat.{u + 1} (Λ l)) AddCommGrpCat.{u + 1})
      (((Prod.sectR n T.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (J T) (coefficientSequenceTopology (J T))).obj
          ((SheafOfModules.toSheaf _).obj M)).property⟩

private def tower (M : Systems T (A l T)) : DiagonalSystems l T where
  obj n := level l T M n.unop
  map {n m} f := ⟨{
    app U := (fixed l T M).map (Prod.mkHom f.unop (𝟙 U.unop)).op
    naturality := by
      intro U V g
      change (fixed l T M).map _ ≫ (fixed l T M).map _ =
        (fixed l T M).map _ ≫ (fixed l T M).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1 }⟩
  map_id n := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (fixed l T M).map_id (op (n.unop, U.unop))
  map_comp {n m k} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (fixed l T M).map (Prod.mkHom (f ≫ g).unop (𝟙 U.unop)).op =
      (fixed l T M).map (Prod.mkHom f.unop (𝟙 U.unop)).op ≫
        (fixed l T M).map (Prod.mkHom g.unop (𝟙 U.unop)).op
    rw [← Functor.map_comp]
    congr 1

private def restrictionFunctor : Systems T (A l T) ⥤ DiagonalSystems l T where
  obj := tower l T
  map {M N} f := {
    app n := ⟨Functor.whiskerLeft (Prod.sectR n.unop T.ProEt).op
      (constantModuleMap (Λ l)
        ((PresheafOfModules.restrictScalars (scalarMap l T)).map f.val))⟩
    naturality := by
      intro n m g
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      exact (constantModuleMap (Λ l)
        ((PresheafOfModules.restrictScalars (scalarMap l T)).map f.val)).naturality
          (Prod.mkHom g.unop (𝟙 U.unop)).op }
  map_id M := by ext n U x; rfl
  map_comp f g := by ext n U x; rfl

private theorem scalarMap_value (n : ℕ) (U : T.ProEtᵒᵖ) (z : Λ l) :
    (scalarMap l T).app (op (n, U.unop)) z =
      ((PadicInt.toZModPow (n + 1) z.down).val : (P l T).obj (op (n, U.unop))) := by
  unfold scalarMap
  change (SpTowerClasses.coefficientMap l (E l) T n).hom.app U
    ((Scheme.purTwistZlReduction T l n).hom.app U
      ((toSheafify (J T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (Λ l)))).app U z)) = _
  let q : CommRingCat.of (Λ l) ⟶
      CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom))
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (J T)
      ((Functor.const T.ProEtᵒᵖ).map q)) U) z
  change (toSheafify (J T) ((Functor.const T.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))).app U
      (ULift.up (PadicInt.toZModPow (n + 1) z.down)) =
    (Scheme.purTwistZlReduction T l n).hom.app U
      ((toSheafify (J T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (Λ l)))).app U z) at h
  rw [← h]
  let : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz : (ULift.up (PadicInt.toZModPow (n + 1) z.down) :
      ULift.{u + 1} (ZMod (l ^ (n + 1)))) =
      ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) := by
    apply ULift.ext
    exact (ZMod.natCast_zmod_val _).symm
  rw [hz]
  simp only [map_natCast]

private abbrev additiveEvaluation (n : ℕ) :=
  SheafOfModules.toSheaf.{u + 1}
      (SemilinearSections.ring (coefficientSequenceTopology (J T))
        (SemilinearSections.systemRing (J T) (B l T) (τ l T))) ⋙
    (Prod.sectR n T.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (J T) (coefficientSequenceTopology (J T))

private theorem additiveEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (additiveEvaluation l T n) ∧
      PreservesFiniteColimits (additiveEvaluation l T n) := by
  let H := (Prod.sectR n T.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (J T) (coefficientSequenceTopology (J T))
  have : PreservesFiniteLimits H := inferInstance
  let : (Prod.sectR n T.ProEt).IsCocontinuous
      (J T) (coefficientSequenceTopology (J T)) := ⟨fun hS ↦ hS⟩
  let : ∀ F : T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Prod.sectR n T.ProEt).op.HasPointwiseRightKanExtension F := fun F X ↦ by
    let : HasLimitsOfShape (StructuredArrow X (Prod.sectR n T.ProEt).op)
        AddCommGrpCat.{u + 1} := HasLimitsOfShape.of_essentiallySmall _ _
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} H :=
    ((Prod.sectR n T.ProEt).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (J T) (coefficientSequenceTopology (J T))).leftAdjoint_preservesColimits
  exact ⟨inferInstance, inferInstance⟩

private theorem restrictionFunctor_exact :
    PreservesFiniteLimits (restrictionFunctor l T) ∧
      PreservesFiniteColimits (restrictionFunctor l T) := by
  have : (diagonalForget l T).ReflectsIsomorphisms := by
    dsimp only [diagonalForget]
    infer_instance
  have hlim (n : ℕᵒᵖ) : PreservesFiniteLimits
      (restrictionFunctor l T ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj n) := by
    let H := restrictionFunctor l T ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj n
    have : PreservesFiniteLimits (H ⋙ diagonalForget l T) :=
      (additiveEvaluation_exact l T n.unop).1
    exact preservesFiniteLimits_of_reflects_of_preserves H (diagonalForget l T)
  have hcolim (n : ℕᵒᵖ) : PreservesFiniteColimits
      (restrictionFunctor l T ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj n) := by
    let H := restrictionFunctor l T ⋙ (evaluation ℕᵒᵖ (DiagonalMod l T)).obj n
    have : PreservesFiniteColimits (H ⋙ diagonalForget l T) :=
      (additiveEvaluation_exact l T n.unop).2
    exact preservesFiniteColimits_of_reflects_of_preserves H (diagonalForget l T)
  exact ⟨preservesFiniteLimits_of_evaluation _ hlim,
    preservesFiniteColimits_of_evaluation _ hcolim⟩

/-- Restriction from the finite integral coefficients to discrete p-adic scalars.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
finite scalar restriction, and `prose-09-21`.
(blueprint: lem-sfb-diagonal-trace-residue-restriction).

Proof: at level n, restrict the finite coefficient action along the ring map
Z_l → O_(ULift Q_l)/(l^(n+1)) and its constant-section map. Retain the section
abelian groups and their restrictions. Compatibility of the quotient maps makes
horizontal transitions linear and defines the strict tower and its morphisms.
The residue of z acts as its natural-number representative, since the coefficient
ring is annihilated by l^(n+1). The construction changes no additive maps, so it
is additive. Kernels are sectionwise and cokernels are additive sheafifications;
forgetting to abelian sheaves reflects their universal properties. Hence the
functor preserves finite limits and finite colimits. This construction requires
neither Chern data nor any completed projection or derived comparison. -/
theorem exists_diagonalTraceResidueRestriction (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) : Nonempty (Restriction l (ULift.{u} (Padic l)) T) := by
  refine ⟨{ F := restrictionFunctor l T
            underlying := fun _ _ _ ↦ rfl
            restrictions := fun _ _ {_ _} _ ↦ HEq.rfl
            transitions := fun _ {_ _} _ _ ↦ HEq.rfl
            morphisms := fun {_ _} _ _ _ ↦ HEq.rfl
            scalars := ?_
            additive := ⟨by intros; ext n U x; rfl⟩
            limits := (restrictionFunctor_exact l T).1
            colimits := (restrictionFunctor_exact l T).2 }⟩
  intro M n U z x
  let y : M.val.obj (op (n, U.unop)) := x
  have h : ((scalarMap l T).app (op (n, U.unop)) z) • y =
      ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • y := by
    rw [scalarMap_value]
    exact Nat.cast_smul_eq_nsmul _ _ y
  exact h

end AlgebraicGeometry.ProEtale.DiagonalTrace
