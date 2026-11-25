/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Data.ZMod.Basic

/-!
# Coinduction from abelian groups to `ℤ/n`-modules

Coinduction `R = Hom_ℤ(ℤ/n, -)` from abelian groups to `ℤ/n`-modules is right adjoint to the
forgetful functor. The counit `R A ⟶ A` is the inclusion of the `n`-torsion `A[n]`
(`forget₂CoindZModAdj_counit_shortExact`), so an `n`-torsion abelian sheaf is the underlying
abelian sheaf of a sheaf of `ℤ/n`-modules (`CategoryTheory.Sheaf.coindCounit`).

## Main definitions

- `coindZMod`: coinduction from abelian groups to `ℤ/n`-modules, right adjoint to the forgetful
  functor (`forget₂CoindZModAdj`).
- `CategoryTheory.Sheaf.coindCounit`: the counit of coinduction on sheaves.
-/

@[expose] public section

open CategoryTheory
universe w

/-- Coinduction from abelian groups to `ℤ/n`-modules, `A ↦ Hom_ℤ(ℤ/n, A)`. -/
noncomputable def coindZMod (n : ℕ) : AddCommGrpCat.{w} ⥤ ModuleCat.{w} (ULift.{w} (ZMod n)) :=
  (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse ⋙
    ModuleCat.coextendScalars (algebraMap ℤ (ULift.{w} (ZMod n)))

noncomputable def forget₂CoindZModAdj (n : ℕ) :
    forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w} ⊣ coindZMod.{w} n :=
  ((ModuleCat.restrictCoextendScalarsAdj.{w} (algebraMap ℤ (ULift.{w} (ZMod n)))).comp
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.toAdjunction).ofNatIsoLeft
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))

/-- An additive map out of `ℤ/n` is determined by its value at `1`. -/
lemma ULift.ZMod.addMonoidHom_ext {n : ℕ} {M : Type*} [AddCommGroup M]
    {φ ψ : ULift.{w} (ZMod n) →+ M} (h : φ 1 = ψ 1) : φ = ψ := by
  ext ⟨x⟩
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  have hk : (⟨(k : ZMod n)⟩ : ULift.{w} (ZMod n)) = k • (1 : ULift.{w} (ZMod n)) := by
    ext; simp
  rw [hk, map_zsmul, map_zsmul, h]

/-- Every `n`-torsion element is the value at `1` of an additive map out of `ℤ/n`. -/
lemma ULift.ZMod.exists_addMonoidHom_apply_one {n : ℕ} {M : Type*} [AddCommGroup M]
    {a : M} (ha : (n : ℤ) • a = 0) : ∃ φ : ULift.{w} (ZMod n) →+ M, φ 1 = a := by
  let g : ℤ →+ M := zmultiplesHom M a
  have hg : g n = 0 := by simpa [g] using ha
  refine ⟨(ZMod.lift n ⟨g, hg⟩).comp (AddEquiv.ulift.toAddMonoidHom), ?_⟩
  change ZMod.lift n ⟨g, hg⟩ ((1 : ULift.{w} (ZMod n)).down) = a
  have : ((1 : ULift.{w} (ZMod n)).down) = ((1 : ℤ) : ZMod n) := by simp
  rw [this, ZMod.lift_coe]
  simp [g]

lemma forget₂CoindZModAdj_counit_app (n : ℕ) (A : AddCommGrpCat.{w}) :
    (forget₂CoindZModAdj.{w} n).counit.app A =
      (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).map
        ((ModuleCat.RestrictionCoextensionAdj.counit'
          (algebraMap ℤ (ULift.{w} (ZMod n)))).app
          ((forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse.obj A)) ≫
        (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.counit.app A := by
  simp [forget₂CoindZModAdj, Adjunction.comp_counit_app, ModuleCat.restrictCoextendScalarsAdj]
  rfl

lemma counit'_app_apply (n : ℕ) (M : ModuleCat.{w} ℤ)
    (φ : (ModuleCat.restrictScalars (algebraMap ℤ (ULift.{w} (ZMod n)))).obj
      ((ModuleCat.coextendScalars (algebraMap ℤ (ULift.{w} (ZMod n)))).obj M)) :
    (ModuleCat.RestrictionCoextensionAdj.counit' (algebraMap ℤ (ULift.{w} (ZMod n)))).app M φ =
      (ModuleCat.CoextendScalars.equiv (algebraMap ℤ (ULift.{w} (ZMod n))) M φ)
        (show _ from (1 : ULift.{w} (ZMod n))) := rfl

lemma forget₂CoindZModAdj_counit_shortExact (n : ℕ) (A : AddCommGrpCat.{w}) :
    Function.Injective ((forget₂CoindZModAdj.{w} n).counit.app A) ∧
      ∀ a : A, (n : ℤ) • a = 0 → a ∈ Set.range ((forget₂CoindZModAdj.{w} n).counit.app A) := by
  set M := (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse.obj A
  set ε := (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.counit.app A
  have hε := ConcreteCategory.bijective_of_isIso ε
  rw [forget₂CoindZModAdj_counit_app]
  refine ⟨fun φ ψ h ↦ ?_, fun a ha ↦ ?_⟩
  · have h' := hε.1 h
    change (ModuleCat.CoextendScalars.equiv _ M φ) (show _ from (1 : ULift.{w} (ZMod n))) =
      (ModuleCat.CoextendScalars.equiv _ M ψ) (show _ from (1 : ULift.{w} (ZMod n))) at h'
    apply (ModuleCat.CoextendScalars.equiv _ M).injective
    exact LinearMap.toAddMonoidHom_injective
      (ULift.ZMod.addMonoidHom_ext.{w} (n := n) (M := M) h')
  · obtain ⟨b, rfl⟩ := hε.2 a
    have hb : (n : ℤ) • b = 0 := hε.1 (by rw [map_zsmul, ha, map_zero])
    obtain ⟨φ, hφ⟩ := ULift.ZMod.exists_addMonoidHom_apply_one.{w} (n := n) (M := M) hb
    refine ⟨(ModuleCat.CoextendScalars.equiv _ M).symm
      { toFun := fun x ↦ φ (show ULift.{w} (ZMod n) from x)
        map_add' := fun x y ↦ φ.map_add _ _
        map_smul' := fun k x ↦ ?_ }, ?_⟩
    · rw [ModuleCat.restrictScalars.smul_def]
      change φ ((algebraMap ℤ (ULift.{w} (ZMod n)) k) * (show ULift.{w} (ZMod n) from x)) = _
      rw [algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul, map_zsmul, RingHom.id_apply]
      exact (int_smul_eq_zsmul _ _ _).symm
    erw [ConcreteCategory.comp_apply]
    refine congrArg ε ?_
    have key : (ModuleCat.RestrictionCoextensionAdj.counit'
        (algebraMap ℤ (ULift.{w} (ZMod n)))).app M ((ModuleCat.CoextendScalars.equiv _ M).symm
          { toFun := fun x ↦ φ (show ULift.{w} (ZMod n) from x)
            map_add' := fun x y ↦ φ.map_add _ _
            map_smul' := fun k x ↦ by
              rw [ModuleCat.restrictScalars.smul_def]
              change φ ((algebraMap ℤ (ULift.{w} (ZMod n)) k) *
                (show ULift.{w} (ZMod n) from x)) = _
              rw [algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul, map_zsmul, RingHom.id_apply]
              exact (int_smul_eq_zsmul _ _ _).symm }) = b := by
      refine (counit'_app_apply n M _).trans ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hφ
    exact key

universe u

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) (n : ℕ)
  [J.HasSheafCompose (coindZMod.{u + 1} n)]

/-- The counit `forget (R F) ⟶ F` of coinduction, a kernel of multiplication by `n`. -/
noncomputable def coindCounit (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{u + 1})).obj
      ((sheafCompose J (coindZMod.{u + 1} n)).obj F) ⟶ F :=
  ⟨Functor.whiskerLeft F.obj (forget₂CoindZModAdj.{u + 1} n).counit⟩

end CategoryTheory.Sheaf
