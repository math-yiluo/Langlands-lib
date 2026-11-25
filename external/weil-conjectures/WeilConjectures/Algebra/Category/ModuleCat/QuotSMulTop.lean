/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Reduction of modules modulo an ideal

For an ideal `I` of a commutative ring `R`, the functor `M ↦ M / I M` from `R`-modules to
`R ⧸ I`-modules (`ModuleCat.quotSMulTop`). It is extension of scalars along `R ⟶ R ⧸ I`; after
restricting scalars back to `R` it is `M ↦ M ⊗_R R ⧸ I`
(`ModuleCat.quotSMulTopCompRestrictScalarsIso`).

Unlike Mathlib's `QuotSMulTop r M = M ⧸ r • ⊤`, which reduces modulo a single element `r`, the
functor here reduces modulo an ideal `I`.

## Main definitions

- `ModuleCat.quotSMulTop`: the functor `M ↦ M / I M`.
- `ModuleCat.quotSMulTopCompRestrictScalarsIso`: its composite with restriction of scalars is
  tensoring with `R ⧸ I`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

open scoped Pointwise

namespace ModuleCat

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The `R ⧸ I`-linear map `M / I M ⟶ N / I N` induced by an `R`-linear map `M ⟶ N`. -/
noncomputable def quotSMulTopMap {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R ⧸ I] (N ⧸ I • (⊤ : Submodule R N)) where
  toFun := Submodule.mapQ _ _ f (by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top)
  map_add' := map_add _
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Module.Quotient.mk_smul_mk]
    simp only [Submodule.mapQ_apply, map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma quotSMulTopMap_mk {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (m : M) :
    quotSMulTopMap I f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) :=
  rfl

/-- The reduction functor `M ↦ M / I M` from `R`-modules to `R ⧸ I`-modules, i.e. extension of
scalars along `R ⟶ R ⧸ I`. It reduces modulo the ideal `I`, not modulo an element as Mathlib's
`QuotSMulTop`. -/
noncomputable def quotSMulTop : ModuleCat.{v} R ⥤ ModuleCat.{v} (R ⧸ I) where
  obj M := ModuleCat.of (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))
  map f := ModuleCat.ofHom (quotSMulTopMap I f.hom)
  map_id M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m => exact quotSMulTopMap_mk I _ m
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m => exact quotSMulTopMap_mk I _ m

@[simp]
lemma quotSMulTop_map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) (m : M) :
    (quotSMulTop I).map f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) :=
  rfl

instance : (quotSMulTop.{v} I).Additive where
  map_add {_ _ f g} := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m => exact quotSMulTopMap_mk I _ m

/-- Restricting the scalars of `M / I M` back to `R` gives `M / I M` as an `R`-module. -/
noncomputable def quotSMulTopRestrictScalarsEquiv (M : Type v) [AddCommGroup M] [Module R M] :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R]
      (restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change _ = Ideal.Quotient.mk I r • Submodule.Quotient.mk m
    rw [Module.Quotient.mk_smul_mk]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Reduction modulo `I` followed by restriction of scalars is tensoring with `R ⧸ I`.** -/
noncomputable def quotSMulTopCompRestrictScalarsIso :
    quotSMulTop.{u} I ⋙ restrictScalars (Ideal.Quotient.mk I) ≅
      tensorRight (ModuleCat.of R (R ⧸ I)) :=
  NatIso.ofComponents (fun M ↦ (LinearEquiv.toModuleIso
    ((TensorProduct.tensorQuotEquivQuotSMul M I).trans
      (quotSMulTopRestrictScalarsEquiv I M))).symm)
    (fun {M N} f ↦ by
      ext x
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change (TensorProduct.tensorQuotEquivQuotSMul N I).symm (Submodule.Quotient.mk (f m)) =
        (f.hom.rTensor _)
          ((TensorProduct.tensorQuotEquivQuotSMul M I).symm (Submodule.Quotient.mk m))
      simp)

end ModuleCat
