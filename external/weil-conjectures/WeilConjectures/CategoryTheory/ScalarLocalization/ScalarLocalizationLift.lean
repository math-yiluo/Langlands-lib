/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization

/-!
# Functors and transformations out of a raw scalar localization

Every morphism of `ScalarLocalization R C p` becomes integral after multiplication by a
power of `p`, and these powers act invertibly. Consequently an arbitrary functor out of the
raw scalar localization is determined by its restriction along `localization R C p`, and a
natural isomorphism between such restrictions extends uniquely.

## Main declarations

* `ScalarLocalization.exists_pow_smul_eq_map`: every fraction is integral after scaling.
* `ScalarLocalization.liftNatIso`: extension of isomorphisms of restrictions.
* `ScalarLocalization.functor_ext`: functors agreeing after localization are equal.
-/

@[expose] public section

universe r u v w x

open TensorProduct

namespace CategoryTheory.ScalarLocalization

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] {p : R}

omit [Category C] [Preadditive C] [Linear R C] in
/-- Every element of a module base-changed to `Localization.Away p` becomes a pure tensor
with first factor one after multiplying by a power of `p`. -/
theorem exists_pow_smul_eq_one_tmul {M : Type w} [AddCommGroup M] [Module R M]
    (z : Localization.Away p ⊗[R] M) :
    ∃ (n : ℕ) (m : M), p ^ n • z = (1 : Localization.Away p) ⊗ₜ[R] m := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers p) a
    obtain ⟨n, hn⟩ := t.2
    dsimp only at hn
    refine ⟨n, s • m, ?_⟩
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def, mul_one, hn]
    exact congrArg (· ⊗ₜ[R] m) (IsLocalization.mk'_spec' (Localization.Away p) s t)
  | add z z' hz hz' =>
    obtain ⟨n, m, hm⟩ := hz
    obtain ⟨n', m', hm'⟩ := hz'
    refine ⟨n + n', p ^ n' • m + p ^ n • m', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hm,
      ← hm', smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n' n]

/-- Every morphism of the raw scalar localization becomes integral after multiplying by a
power of the localized element. -/
theorem exists_pow_smul_eq_map {K L : ScalarLocalization R C p} (f : K ⟶ L) :
    ∃ (n : ℕ) (g : K.obj ⟶ L.obj), p ^ n • f = (localization R C p).map g :=
  exists_pow_smul_eq_one_tmul (M := K.obj ⟶ L.obj) f

/-- Multiplication by a power of the localized element is invertible after localization. -/
theorem isIso_map_pow_smul_id (n : ℕ) (K : C) :
    IsIso ((localization R C p).map (p ^ n • 𝟙 K)) := by
  have hp : p ^ n • (IsLocalization.Away.invSelf p : Localization.Away p) ^ n = 1 := by
    rw [Algebra.smul_def, map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  refine ⟨⟨((IsLocalization.Away.invSelf p : Localization.Away p) ^ n) ⊗ₜ[R] 𝟙 K,
    ?_, ?_⟩⟩
  · change composition R C p K K K (_ ⊗ₜ[R] 𝟙 K)
      ((1 : Localization.Away p) ⊗ₜ[R] (p ^ n • 𝟙 K)) =
        (1 : Localization.Away p) ⊗ₜ[R] 𝟙 K
    rw [composition_tmul, mul_one, Category.comp_id, ← TensorProduct.smul_tmul, hp]
  · change composition R C p K K K ((1 : Localization.Away p) ⊗ₜ[R] (p ^ n • 𝟙 K))
      (_ ⊗ₜ[R] 𝟙 K) = (1 : Localization.Away p) ⊗ₜ[R] 𝟙 K
    rw [composition_tmul, one_mul, Category.id_comp, ← TensorProduct.smul_tmul, hp]

variable {D : Type w} [Category.{x} D]

/-- An isomorphism of restrictions along the localization extends to the functors themselves,
with the same components. -/
noncomputable def liftNatIso (B B' : ScalarLocalization R C p ⥤ D)
    (c : localization R C p ⋙ B ≅ localization R C p ⋙ B') : B ≅ B' :=
  NatIso.ofComponents (fun K ↦ c.app K.obj) (fun {K L} f ↦ by
    obtain ⟨n, g, hg⟩ := exists_pow_smul_eq_map f
    have hs : (localization R C p).map (p ^ n • 𝟙 K.obj) ≫ f =
        (localization R C p).map g := by
      rw [Functor.map_smul, Functor.map_id]
      erw [Linear.smul_comp, Category.id_comp]
      exact hg
    have := isIso_map_pow_smul_id (R := R) (C := C) (p := p) n K.obj
    have h1 := c.hom.naturality g
    have h2 := c.hom.naturality (p ^ n • 𝟙 K.obj)
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi (B.map ((localization R C p).map (p ^ n • 𝟙 K.obj)))).1
    simp only [Iso.app_hom]
    exact (B.map_comp_assoc _ _ _).symm.trans
      ((congrArg (fun φ ↦ B.map φ ≫ c.hom.app L.obj) hs).trans
      (h1.trans ((congrArg (fun φ ↦ c.hom.app K.obj ≫ B'.map φ) hs.symm).trans
      ((congrArg (c.hom.app K.obj ≫ ·) (B'.map_comp _ _)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ B'.map f) h2.symm).trans (Category.assoc _ _ _))))))))

@[simp]
theorem liftNatIso_hom_app (B B' : ScalarLocalization R C p ⥤ D)
    (c : localization R C p ⋙ B ≅ localization R C p ⋙ B') (K : ScalarLocalization R C p) :
    (liftNatIso B B' c).hom.app K = c.hom.app K.obj :=
  rfl

/-- Functors out of a raw scalar localization are determined by their restrictions along the
localization functor; no additivity is required. -/
theorem functor_ext {B B' : ScalarLocalization R C p ⥤ D}
    (h : localization R C p ⋙ B = localization R C p ⋙ B') : B = B' :=
  Functor.ext_of_iso (liftNatIso B B' (eqToIso h))
    (fun K ↦ congrArg (fun J ↦ J.obj K.obj) h)
    (fun K ↦ eqToHom_app h K.obj)

end CategoryTheory.ScalarLocalization
