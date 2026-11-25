/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits

import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientTensor
import WeilConjectures.CategoryTheory.Tensor.TensorPushoutAction
public import WeilConjectures.AlgebraicGeometry.PurTwistSheaves

/-! # The integral Tate line on the pro-etale site

The auxiliary constructions retain the root tower, constant scalar extension and completed
scalar action. All choices below have a uniqueness specification. The tensor of commutative
ring sheaves is their pushout, so the coefficient comparison is a morphism of ring sheaves.
The natural-number level `n` means positive exponent `n + 1` throughout.

## Main definitions

* `purTwistZlOne` and `purTwistZlModule`: the root limit and its completed scalar action.
* `purTwistIntegralOne` and `purTwistIntegralModule`: the prescribed integral tensor line.
* `purTwistFiniteOne`: its prescribed ordinary finite-coefficient tensor reduction.
The coefficient rings and their comparison are reexported from
`WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement`.
Local freeness and derived completeness
are proved in `WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree`.

## References

* Stacks Tag 03PK
* Stacks Tag 03EK
-/

@[expose] public section

set_option autoImplicit false

universe u d

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The original root tower's inverse limit, with no replacement of its underlying groups. -/
noncomputable def purTwistZlOne :=
  limit (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))

set_option backward.isDefEq.respectTransparency.types false in
-- Pull back the target action along the coefficient reduction. Normalized torsion
-- actions make every additive sheaf morphism linear for this pulled-back action.
private theorem purTwistTorsionMap_smul
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J RingCat.{u + 1}] (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (F G : Sheaf J AddCommGrpCat.{u + 1})
    (hF : ∀ U (x : F.obj.obj U), N' • x = 0)
    (hG : ∀ U (x : G.obj.obj U), N • x = 0)
    (hG' : ∀ U (x : G.obj.obj U), N' • x = 0)
    (ρ : constantZModRingSheaf J N' ⟶
      constantZModRingSheaf J N) (φ : F ⟶ G)
    (U : Cᵒᵖ) (a : (constantZModRingSheaf J N').obj.obj U)
    (x : F.obj.obj U) :
    φ.hom.app U
      (@SMul.smul _ _ (torsionSheafModuleStructure J N' hN' F hF U).toSMul
        a x) =
      @SMul.smul _ _ (torsionSheafModuleStructure J N hN G hG U).toSMul
        (ρ.hom.app U a) (φ.hom.app U x) := by
  let M (V : Cᵒᵖ) := torsionSheafModuleStructure J N hN G hG V
  let M' (V : Cᵒᵖ) :
      Module ((constantZModRingSheaf J N').obj.obj V) (G.obj.obj V) :=
    letI := M V
    Module.compHom _ (ρ.hom.app V).hom
  have hM' : IsConstantZModSheafModuleStructure J N' G M' := by
    constructor
    · intro V z y
      change @SMul.smul _ _ (M V).toSMul (ρ.hom.app V
        (((toSheafify J
          ((Functor.const Cᵒᵖ).obj
            (RingCat.of (ULift.{u + 1} (ZMod N'))))).app V).hom
          (z : ULift.{u + 1} (ZMod N')))) y = z • y
      rw [map_intCast, map_intCast]
      exact @Int.cast_smul_eq_zsmul _ _ _ _ (M V) z y
    · intro V W f b y
      change G.obj.map f (@SMul.smul _ _ (M V).toSMul (ρ.hom.app V b) y) =
        @SMul.smul _ _ (M W).toSMul
          (ρ.hom.app W ((constantZModRingSheaf J N').obj.map f b))
          (G.obj.map f y)
      rw [(torsionSheafModuleStructure_spec J N hN G hG).2 f]
      rw [NatTrans.naturality_apply ρ.hom f]
  exact torsionSheaf_hom_linear J N' hN' F G hF hG' φ
    (torsionSheafModuleStructure J N' hN' F hF) M'
    (torsionSheafModuleStructure_spec J N' hN' F hF) hM' U a x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem purTwistTransition_smul (n : ℕ) (U : S.ProEtᵒᵖ)
    (a : (purTwistFiniteRing S l (n + 1)).obj.obj U)
    (x : (purTwistRootsModule S l (n + 1)).val.obj U) :
    (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U (a • x) =
      (purTwistFiniteTransition S l n).hom.app U a •
        (@id ((purTwistRootsModule S l n).val.obj U)
          ((proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
            (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
            (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U x)) := by
  let ρ := (purTwistFiniteRingIso S l (n + 1)).inv ≫
    (sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistFiniteTransition S l n) ≫ (purTwistFiniteRingIso S l n).hom
  have h := purTwistTorsionMap_smul (ProEt.topology S) (l ^ (n + 1)) (l ^ (n + 2))
    (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
    _ _ (proEtaleRootsOfUnity_nsmul S _) (proEtaleRootsOfUnity_nsmul S _)
    (proEtaleRootsOfUnity_nsmul_of_dvd S _ _ (pow_dvd_pow l (Nat.le_succ (n + 1))))
    ρ (proEtaleRootsOfUnityTransition S _ _
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1)))) U
    ((purTwistFiniteRingIso S l (n + 1)).hom.hom.app U a) x
  have he : ρ.hom.app U ((purTwistFiniteRingIso S l (n + 1)).hom.hom.app U a) =
      (purTwistFiniteRingIso S l n).hom.hom.app U
        ((purTwistFiniteTransition S l n).hom.app U a) := by
    change ((purTwistFiniteRingIso S l n).hom.hom.app U)
      ((purTwistFiniteTransition S l n).hom.app U
        (((purTwistFiniteRingIso S l (n + 1)).hom ≫
          (purTwistFiniteRingIso S l (n + 1)).inv).hom.app U a)) = _
    rw [Iso.hom_inv_id]
    rfl
  rw [he] at h
  exact h

-- Jointly injective coordinates transfer the module laws and determine the action uniquely.
private theorem purTwistCoordinateModule
    {R M : Type*} [CommRing R] [AddCommGroup M]
    {A : ℕ → Type*} [∀ n, CommRing (A n)]
    {N : ℕ → Type*} [∀ n, AddCommGroup (N n)] [∀ n, Module (A n) (N n)]
    (p : ∀ n, M →+ N n) (q : ∀ n, R →+* A n)
    (hext : ∀ x y, (∀ n, p n x = p n y) → x = y)
    (hs : ∀ a x, ∃ y, ∀ n, p n y = q n a • p n x) :
    ∃! m : Module R M, ∀ n a x, p n (@SMul.smul _ _ m.toSMul a x) = q n a • p n x := by
  classical
  choose sm hsm using hs
  let m : Module R M :=
    { smul := sm
      one_smul := by
        intro x
        apply hext
        intro n
        change p n (sm 1 x) = p n x
        rw [hsm, map_one, one_smul]
      mul_smul := by
        intro a b x
        apply hext
        intro n
        change p n (sm (a * b) x) = p n (sm a (sm b x))
        rw [hsm, hsm, hsm, map_mul, mul_smul]
      smul_zero := by
        intro a
        apply hext
        intro n
        change p n (sm a 0) = p n 0
        rw [hsm, map_zero, smul_zero]
      smul_add := by
        intro a x y
        apply hext
        intro n
        change p n (sm a (x + y)) = p n (sm a x + sm a y)
        rw [hsm, map_add, map_add, hsm, hsm, smul_add]
      add_smul := by
        intro a b x
        apply hext
        intro n
        change p n (sm (a + b) x) = p n (sm a x + sm b x)
        rw [hsm, map_add, map_add, hsm, hsm, add_smul]
      zero_smul := by
        intro x
        apply hext
        intro n
        change p n (sm 0 x) = p n 0
        rw [hsm, map_zero, zero_smul, map_zero] }
  refine ⟨m, (fun n a x ↦ hsm a x n), ?_⟩
  intro m' hm'
  apply Module.ext'
  intro a x
  apply hext
  intro n
  exact (hm' n a x).trans (hsm a x n).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The completed scalar action is determined coordinatewise on the root limit. -/
theorem purTwistZlAction_existsUnique :
    ∃! M : ∀ U : S.ProEtᵒᵖ,
      Module ((purTwistZlCompletion S l).obj.obj U) ((purTwistZlOne S l).obj.obj U),
      (∀ ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
        (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U),
        (purTwistZlOne S l).obj.map f (@SMul.smul _ _ (M U).toSMul a x) =
          @SMul.smul _ _ (M V).toSMul ((purTwistZlCompletion S l).obj.map f a)
            ((purTwistZlOne S l).obj.map f x)) ∧
      ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
        (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U),
        (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
          (@SMul.smul _ _ (M U).toSMul a x) =
        ((purTwistZlProjection S l n).hom.app U a) •
          (@id ((purTwistRootsModule S l n).val.obj U)
            ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
              U x)) := by
  classical
  let T : ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
    proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)
  let ev (U : S.ProEtᵒᵖ) :
      Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation S.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj U
  let p (n : ℕ) (U : S.ProEtᵒᵖ) : (purTwistZlOne S l).obj.obj U →+
      (purTwistRootsModule S l n).val.obj U := ((limit.π T (op n)).hom.app U).hom
  let q (n : ℕ) (U : S.ProEtᵒᵖ) : (purTwistZlCompletion S l).obj.obj U →+*
      (purTwistFiniteRing S l n).obj.obj U := ((purTwistZlProjection S l n).hom.app U).hom
  have hxext (U : S.ProEtᵒᵖ) (x y : (purTwistZlOne S l).obj.obj U)
      (h : ∀ n, p n U x = p n U y) : x = y := by
    exact Concrete.isLimit_ext (T ⋙ ev U)
      (isLimitOfPreserves (ev U) (limit.isLimit T)) x y (fun n ↦ h n.unop)
  have hp (n : ℕ) (U : S.ProEtᵒᵖ) (x : (purTwistZlOne S l).obj.obj U) :
      (T.map (homOfLE (Nat.le_succ n)).op).hom.app U (p (n + 1) U x) = p n U x := by
    exact congrArg (fun f ↦ f.hom.app U x) (limit.w T (homOfLE (Nat.le_succ n)).op)
  have hq (n : ℕ) (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U) :
      (purTwistFiniteTransition S l n).hom.app U (q (n + 1) U a) = q n U a := by
    have h := limit.w (purTwistZlTower S l) (homOfLE (Nat.le_succ n)).op
    rw [show (purTwistZlTower S l).map (homOfLE (Nat.le_succ n)).op =
      purTwistFiniteTransition S l n from Functor.ofOpSequence_map_homOfLE_succ _ n] at h
    exact congrArg (fun f ↦ f.hom.app U a) h
  have hs (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U)
      (x : (purTwistZlOne S l).obj.obj U) :
      ∃ y : (purTwistZlOne S l).obj.obj U,
        ∀ n, p n U y = q n U a • (@id ((purTwistRootsModule S l n).val.obj U) (p n U x)) := by
    let c : Cone (T ⋙ ev U ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      { pt := PUnit
        π := NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ q n U a •
          (@id ((purTwistRootsModule S l n).val.obj U) (p n U x))) (by
          intro n
          ext z
          change q n U a • (@id ((purTwistRootsModule S l n).val.obj U) (p n U x)) =
            (T.map (homOfLE (Nat.le_succ n)).op).hom.app U
              (q (n + 1) U a •
                (@id ((purTwistRootsModule S l (n + 1)).val.obj U) (p (n + 1) U x)))
          rw [show (T.map (homOfLE (Nat.le_succ n)).op) =
            proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.le_succ (n + 1))) by
                exact Functor.ofOpSequence_map_homOfLE_succ _ n]
          erw [purTwistTransition_smul]
          rw [hq]
          have hpx := hp n U x
          rw [show T.map (homOfLE (Nat.le_succ n)).op =
            proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.le_succ (n + 1))) from
                Functor.ofOpSequence_map_homOfLE_succ _ n] at hpx
          exact congrArg (fun y : (purTwistRootsModule S l n).val.obj U ↦ q n U a • y)
            hpx.symm) }
    let hc₁ := isLimitOfPreserves (ev U) (limit.isLimit T)
    let hc := isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1}) hc₁
    exact ⟨hc.lift c PUnit.unit, fun n ↦ ConcreteCategory.congr_hom (hc.fac c (op n)) PUnit.unit⟩
  have hmod (U : S.ProEtᵒᵖ) := purTwistCoordinateModule
    (R := (purTwistZlCompletion S l).obj.obj U) (M := (purTwistZlOne S l).obj.obj U)
    (A := fun n ↦ (purTwistFiniteRing S l n).obj.obj U)
    (N := fun n ↦ (purTwistRootsModule S l n).val.obj U)
    (p := fun n ↦ p n U) (q := fun n ↦ q n U) (hxext U) (hs U)
  choose M hM huniq using hmod
  refine ⟨M, ⟨?_, fun n U a x ↦ hM U n a x⟩, ?_⟩
  · intro U V f a x
    apply hxext V
    intro n
    have hn (y : (purTwistZlOne S l).obj.obj U) :
        p n V ((purTwistZlOne S l).obj.map f y) =
          (purTwistRootsModule S l n).val.map f (p n U y) :=
      NatTrans.naturality_apply (limit.π T (op n)).hom f y
    have hqn := (NatTrans.naturality_apply (purTwistZlProjection S l n).hom f a).symm
    rw [hn, hM, hM, (purTwistRootsModule S l n).val.map_smul, ← hqn, hn]
    rfl
  · intro M' hM'
    funext U
    exact huniq U (M' U) (fun n a x ↦ hM'.2 n U a x)

/-- The unique coordinatewise completed coefficient action. -/
@[instance_reducible]
noncomputable def purTwistZlAction := (purTwistZlAction_existsUnique S l).exists.choose

/-- The action commutes with restriction. -/
theorem purTwistZlAction_restriction ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
    (a : (purTwistZlCompletion S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U) :
    (purTwistZlOne S l).obj.map f
      (@SMul.smul _ _ (purTwistZlAction S l U).toSMul a x) =
    @SMul.smul _ _ (purTwistZlAction S l V).toSMul
      ((purTwistZlCompletion S l).obj.map f a) ((purTwistZlOne S l).obj.map f x) := by
  exact (purTwistZlAction_existsUnique S l).exists.choose_spec.1 f a x

/-- `Z_l(1)` as a module over the completed coefficient sheaf, with unchanged root limit. -/
noncomputable def purTwistZlModule :
    SheafOfModules.{u + 1} (purTwistRing S (purTwistZlCompletion S l)) :=
  letI : ∀ U : S.ProEtᵒᵖ,
      Module ((purTwistRing S (purTwistZlCompletion S l)).obj.obj U)
        ((purTwistZlOne S l).obj.obj U) := purTwistZlAction S l
  ⟨PresheafOfModules.ofPresheaf
    (R := (purTwistRing S (purTwistZlCompletion S l)).obj) (purTwistZlOne S l).obj
    (purTwistZlAction_restriction S l), (purTwistZlOne S l).property⟩

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The integral Tate line is the prescribed scalar extension over the discrete constants. -/
noncomputable def purTwistIntegralOne :
    SheafOfModules.{u + 1} (purTwistRing S (purTwistIntegralConstant S l E)) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap S l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l))

/-- A pure tensor in the prescribed integral line, after sheafification. -/
noncomputable def purTwistIntegralTensor (U : S.ProEtᵒᵖ)
    (b : (purTwistIntegralConstant S l E).obj.obj U)
    (x : (purTwistZlModule S l).val.obj U) :
    (purTwistIntegralOne S l E).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (purTwistRing S (purTwistIntegralConstant S l E)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistConstantIntegersMap S l E)
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (ProEt.topology S)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)))).app U)
      (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U,
        ((purTwistConstantIntegersMap S l E).hom.app U).hom] x)

/-- The completed action on the integral tensor is uniquely fixed on pure tensors. -/
theorem purTwistIntegralAction_existsUnique :
    ∃! M : ∀ U : S.ProEtᵒᵖ,
      Module ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        ((purTwistIntegralOne S l E).val.obj U),
      (∀ ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
        (a : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        (x : (purTwistIntegralOne S l E).val.obj U),
        (purTwistIntegralOne S l E).val.map f (@SMul.smul _ _ (M U).toSMul a x) =
          @SMul.smul _ _ (M V).toSMul
            ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.map f a)
            ((purTwistIntegralOne S l E).val.map f x)) ∧
      (∀ (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistIntegralOne S l E).val.obj U),
        @SMul.smul _ _ (M U).toSMul
          ((purTwistIntegralCompletionMap S l E).hom.app U b) x = b • x) ∧
      ∀ (U : S.ProEtᵒᵖ) (a : (purTwistZlCompletion S l).obj.obj U)
        (b : (purTwistIntegralConstant S l E).obj.obj U)
        (x : (purTwistZlModule S l).val.obj U),
        @SMul.smul _ _ (M U).toSMul ((purTwistCompletedScalarMap S l E).hom.app U a)
          (purTwistIntegralTensor S l E U b x) =
        purTwistIntegralTensor S l E U b (a • x) := by
  let e (U : S.ProEtᵒᵖ) :=
    letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    letI := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
    RingEquiv.ofBijective (purTwistCoefficientTensorMap S l E U)
      (purTwistCoefficientTensor S l E U)
  have he (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S l E).obj.obj U)
      (a : (purTwistZlCompletion S l).obj.obj U) :
      letI := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
      letI := ((purTwistZlCompletionMap S l).hom.app U).hom.toAlgebra
      e U (b ⊗ₜ[(purTwistZlConstant S l).obj.obj U] a) =
        (purTwistIntegralCompletionMap S l E).hom.app U b *
          (purTwistCompletedScalarMap S l E).hom.app U a := rfl
  exact CategoryTheory.tensorPushoutAction_existsUnique
    (purTwistZlCompletionMap S l) (purTwistConstantIntegersMap S l E)
    (purTwistCompletedScalarMap S l E) (purTwistIntegralCompletionMap S l E)
    (purTwistZlModule S l) e he

/-- The unique action on the concrete integral tensor sheaf. -/
@[instance_reducible]
noncomputable def purTwistIntegralAction :=
  (purTwistIntegralAction_existsUnique S l E).exists.choose

/-- The integral action commutes with restriction. -/
theorem purTwistIntegralAction_restriction ⦃U V : S.ProEtᵒᵖ⦄ (f : U ⟶ V)
    (a : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
    (x : (purTwistIntegralOne S l E).val.obj U) :
    (purTwistIntegralOne S l E).val.map f
      (@SMul.smul _ _ (purTwistIntegralAction S l E U).toSMul a x) =
    @SMul.smul _ _ (purTwistIntegralAction S l E V).toSMul
      ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.map f a)
      ((purTwistIntegralOne S l E).val.map f x) := by
  exact (purTwistIntegralAction_existsUnique S l E).exists.choose_spec.1 f a x

/-- The prescribed integral tensor equipped with its canonical completed-ring action. -/
noncomputable def purTwistIntegralModule :
    SheafOfModules.{u + 1}
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S) :=
  letI : ∀ U : S.ProEtᵒᵖ,
      Module ((WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
        ((purTwistIntegralOne S l E).val.presheaf.obj U) := purTwistIntegralAction S l E
  ⟨PresheafOfModules.ofPresheaf
    (R := (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S).obj)
    (purTwistIntegralOne S l E).val.presheaf
    (purTwistIntegralAction_restriction S l E), (purTwistIntegralOne S l E).isSheaf⟩

/-- The finite Tate line, the ordinary constant-coefficient tensor reduction at level `n`. -/
noncomputable def purTwistFiniteOne (n : ℕ) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E S n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistIntegralQuotient S l E n)
    (purTwistIntegralOne S l E)

end AlgebraicGeometry.Scheme
