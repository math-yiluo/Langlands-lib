/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Mathlib.CategoryTheory.Functor.OfSequence

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting

/-!
# Inverting the prime in the integral pro-étale coefficient ring

The main theorem exhibits the specified fraction cocone on E_X as a colimit and identifies any
colimit equipped with its localization ring structure with E_X as a ring object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The regular integral coefficient module on X. -/
abbrev padicIntegersRegularModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)

/-- The existing coefficient ring E_X as an integral module along the specified inclusion φ. -/
abbrev padicSubfieldIntegralModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X))

/-- The sequence of regular integral modules with transition multiplication by ℓ. -/
abbrev padicIntegersEllSequence (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (padicIntegersRegularModule X ℓ E))

private theorem scalar_colimit_hom_ext
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (p : ℕ) (M : C) (c : Cocone (Functor.ofSequence (fun _ ↦ p • 𝟙 M)))
    (hc : IsColimit c) (F : C ⥤ D) [F.Additive]
    [PreservesColimit (Functor.ofSequence (fun _ ↦ p • 𝟙 M)) F]
    {B : D} [IsIso (p • 𝟙 B)] (f g : F.obj c.pt ⟶ B)
    (hzero : F.map (c.ι.app 0) ≫ f = F.map (c.ι.app 0) ≫ g) : f = g := by
  apply (isColimitOfPreserves F hc).hom_ext
  intro n
  change F.map (c.ι.app n) ≫ f = F.map (c.ι.app n) ≫ g
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have hs : p • c.ι.app (n + 1) = c.ι.app n := by
      have h := c.w (homOfLE (Nat.le_succ n))
      rw [Functor.ofSequence_map_homOfLE_succ] at h
      change (p • 𝟙 M) ≫ (c.ι.app (n + 1) : M ⟶ c.pt) = c.ι.app n at h
      rw [Preadditive.nsmul_comp, Category.id_comp] at h
      exact h
    apply (cancel_mono (p • 𝟙 B)).1
    simp only [Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, ← F.map_nsmul, hs]
    exact ih

private theorem padicIntegers_cocone (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ α : padicIntegersEllSequence X ℓ E ⟶
        (Functor.const ℕ).obj (padicSubfieldIntegralModule X ℓ E),
      Nonempty (IsColimit
        ({ pt := padicSubfieldIntegralModule X ℓ E, ι := α } :
          Cocone (padicIntegersEllSequence X ℓ E))) ∧
      (α.app 0).hom = padicIntegersToPadicSubfield X ℓ E := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨c, ⟨hc⟩, e, he⟩ := CondensedRing.integralRegularTelescope ℓ E.1 X
  exact ⟨(c.extend e.hom).ι, ⟨hc.ofIsoColimit (Cocone.ext e)⟩, he⟩

/-- E_X is the localization of the integral coefficient sheaf at ℓ, with fraction maps
ℓ⁻ᵐφ, and is flat over that integral sheaf: the cocone `j ≫ t^m` (with `t` inverse to
multiplication by ℓ) is a colimit, any colimit carrying its localization ring structure is
isomorphic to E_X as a ring object, and extension of scalars to E_X is exact. -/
theorem padicIntegers_invertEll (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ j : padicIntegersRegularModule X ℓ E ⟶ padicSubfieldIntegralModule X ℓ E,
      j.hom = padicIntegersToPadicSubfield X ℓ E ∧
      ∃ t : End (padicSubfieldIntegralModule X ℓ E),
        (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E)) ≫ t.asHom = 𝟙 _ ∧
        t.asHom ≫ (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E)) = 𝟙 _ ∧
        ∃ α : padicIntegersEllSequence X ℓ E ⟶
            (Functor.const ℕ).obj (padicSubfieldIntegralModule X ℓ E),
          (∀ m : ℕ, α.app m = j ≫ (t ^ m).asHom) ∧
          Nonempty (IsColimit
            ({ pt := padicSubfieldIntegralModule X ℓ E, ι := α } :
              Cocone (padicIntegersEllSequence X ℓ E))) ∧
          (∀ (c : Cocone (padicIntegersEllSequence X ℓ E)), IsColimit c →
            ∀ [MonObj c.pt.X] [IsCommMonObj c.pt.X],
              IsMonHom (@id
                (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶ c.pt.X)
                (c.ι.app 0).hom) →
              ∃ e : Mon.mk c.pt.X ≅
                  Mon.mk (condensedRingObj (Profinite.continuousMapRingObj E.1) X),
                ∀ m : ℕ, (c.ι.app m).hom ≫ e.hom.hom = (α.app m).hom) ∧
          PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨α, ⟨hα⟩, hzero⟩ := padicIntegers_cocone X ℓ E
  let c : Cocone (padicIntegersEllSequence X ℓ E) :=
    { pt := padicSubfieldIntegralModule X ℓ E, ι := α }
  have : IsIso (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E)) := by
    have := CondensedRing.module_nsmul_isIso ℓ E.1 X
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    have h := (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).map_isIso
      (ℓ • 𝟙 (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X)))
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using h
  let t : End (padicSubfieldIntegralModule X ℓ E) := .of (inv (ℓ • 𝟙 _))
  have hpow (n : ℕ) : α.app n = α.app 0 ≫ (t ^ n).asHom := by
    induction n with
    | zero => simp [End.one_asHom]
    | succ n ih =>
      have hn := c.w (homOfLE (Nat.le_succ n))
      dsimp only [padicIntegersEllSequence] at hn
      rw [Functor.ofSequence_map_homOfLE_succ] at hn
      change (ℓ • 𝟙 (padicIntegersRegularModule X ℓ E)) ≫
        (α.app (n + 1) : padicIntegersRegularModule X ℓ E ⟶
          padicSubfieldIntegralModule X ℓ E) = α.app n at hn
      rw [Preadditive.nsmul_comp, Category.id_comp] at hn
      have hn' : (α.app (n + 1) : padicIntegersRegularModule X ℓ E ⟶
          padicSubfieldIntegralModule X ℓ E) ≫
          (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E)) = α.app n := by
        dsimp only [padicIntegersEllSequence, Functor.ofSequence_obj,
          Functor.const_obj_obj] at hn ⊢
        rw [Preadditive.comp_nsmul, Category.comp_id]
        exact hn
      rw [pow_succ', End.mul_asHom, ← Category.assoc, ← ih]
      apply (cancel_mono (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E))).1
      dsimp only [t]
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hn']
  refine ⟨α.app 0, hzero, t, IsIso.hom_inv_id _, IsIso.inv_hom_id _,
    α, hpow, ⟨hα⟩, ?_, CondensedRing.integralScalarExtension_exact ℓ E.1 X⟩
  intro d hd instMon instComm hMon
  let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X
  let B := condensedRingObj (Profinite.continuousMapRingObj E.1) X
  let V := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  let e : d.pt.X ≅ B := V.mapIso (hd.coconePointUniqueUpToIso hα)
  let a : R ⟶ d.pt.X := (d.ι.app 0).hom
  have he (n : ℕ) : (d.ι.app n).hom ≫ e.hom = (α.app n).hom := by
    exact congrArg (fun f ↦ f.hom) (hd.comp_coconePointUniqueUpToIso_hom hα n)
  have hzero' : a ≫ e.hom = padicIntegersToPadicSubfield X ℓ E := by
    exact (he 0).trans hzero
  have : IsIso (ℓ • 𝟙 B) := by
    have h := V.map_isIso (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E))
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] at h
    exact h
  have hMon' : IsMonHom a := hMon
  have hunit : MonObj.one (X := d.pt.X) ≫ e.hom = MonObj.one (X := B) := by
    rw [← IsMonHom.one_hom a, Category.assoc, hzero',
      IsMonHom.one_hom]
  have hmul : MonObj.mul (X := d.pt.X) ≫ e.hom =
      (e.hom ⊗ₘ e.hom) ≫ MonObj.mul (X := B) := by
    apply scalar_colimit_hom_ext ℓ (padicIntegersRegularModule X ℓ E) d hd
      (V ⋙ tensorRight d.pt.X)
    change (a ▷ d.pt.X) ≫ MonObj.mul ≫ e.hom =
      (a ▷ d.pt.X) ≫ (e.hom ⊗ₘ e.hom) ≫ MonObj.mul
    apply scalar_colimit_hom_ext ℓ (padicIntegersRegularModule X ℓ E) d hd
      (V ⋙ tensorLeft R)
    change (R ◁ a) ≫
        (a ▷ d.pt.X) ≫ MonObj.mul ≫ e.hom =
      (R ◁ a) ≫
        (a ▷ d.pt.X) ≫ (e.hom ⊗ₘ e.hom) ≫ MonObj.mul
    rw [← tensorHom_def'_assoc, ← tensorHom_def'_assoc,
      ← IsMonHom.mul_hom_assoc, hzero', tensorHom_comp_tensorHom_assoc,
      hzero', IsMonHom.mul_hom]
  exact ⟨Mon.mkIso e hunit hmul, he⟩

end AlgebraicGeometry.ProEtale
