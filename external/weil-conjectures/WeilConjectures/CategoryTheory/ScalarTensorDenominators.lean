/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-! # Clearing denominators in a tensor-Hom coefficient comparison

Source: current blueprint sk-prop-sp-rational-adjunction, its clearing-denominators
argument (blueprint: lem-sp-scalar-tensor-denominators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
namespace CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

/-- A tensor-Hom equivalence gives common prime-power denominators and detects
exactly prime-power torsion in the kernel on integral arrows.
Source: the denominator argument in sk-prop-sp-rational-adjunction.
Proof: identify each target Hom group with the corresponding raw tensor module
using the equivalence and its specified comparison on integral objects. Module
localization clears a denominator of an arbitrary tensor and detects equality
of tensors with coefficient one. Since the denominator is a power of a natural
number, its action is repeated addition; the additive Hom identification
preserves that action. Naturality identifies coefficient-one tensors with the
original functor's arrows.
(blueprint: lem-sp-scalar-tensor-denominators). -/
theorem scalarTensor_denominators
    (R : Type*) [CommRing R] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Linear R C] [Preadditive D] [HasBinaryProducts D]
    (p : ℕ) (F : C ⥤ D)
    (e : ScalarLocalization R C (p : R) ≌ D)
    (c : ScalarLocalization.localization R C (p : R) ⋙ e.functor ≅ F) :
    (∀ (X Y : C) (z : F.obj X ⟶ F.obj Y),
      ∃ (n : ℕ) (g : X ⟶ Y), p ^ n • z = F.map g) ∧
    (∀ (X Y : C) (f g : X ⟶ Y), F.map f = F.map g →
      ∃ n : ℕ, p ^ n • f = p ^ n • g) := by
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  have : e.functor.Additive := e.symm.inverse_additive
  let H (X Y : C) :
      (ScalarLocalization.mk X ⟶ ScalarLocalization.mk Y) ≃ₗ[ℤ]
        (F.obj X ⟶ F.obj Y) :=
    (LinearEquiv.ofBijective (e.functor.mapLinearMap ℤ)
      e.fullyFaithfulFunctor.homEquiv.bijective).trans
        (Linear.homCongr ℤ (c.app X) (c.app Y))
  have hmap (X Y : C) (g : X ⟶ Y) : H X Y (1 ⊗ₜ[R] g) = F.map g := by
    change (c.inv.app X ≫ e.functor.map
      ((ScalarLocalization.localization R C (p : R)).map g)) ≫ c.hom.app Y = F.map g
    rw [Category.assoc, ← Functor.comp_map, c.hom.naturality,
      Iso.inv_hom_id_app_assoc]
  constructor
  · intro X Y z
    let t := (H X Y).symm z
    obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers (p : R))
      (TensorProduct.mk R (Localization.Away (p : R)) (X ⟶ Y) 1) t
    obtain ⟨n, hn⟩ := s.property
    have ht : p ^ n • t = (1 : Localization.Away (p : R)) ⊗ₜ[R] g := by
      simpa only [Submonoid.smul_def, ← hn, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul,
        TensorProduct.mk_apply] using hs
    refine ⟨n, g, ?_⟩
    have hh := congrArg (H X Y) ht
    simpa only [map_nsmul, hmap, t, LinearEquiv.apply_symm_apply] using hh
  · intro X Y f g hfg
    have he : (1 : Localization.Away (p : R)) ⊗ₜ[R] f = 1 ⊗ₜ[R] g :=
      (H X Y).injective (by simpa only [hmap] using hfg)
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (p : R)
      (f := TensorProduct.mk R (Localization.Away (p : R)) (X ⟶ Y) 1) he
    exact ⟨n, by simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hn⟩

end CategoryTheory
