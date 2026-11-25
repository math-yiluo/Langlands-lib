/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import WeilConjectures.CategoryTheory.DerivedCategory.ExtendScalarsLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.PrincipalIdealDevissage
public import WeilConjectures.CategoryTheory.Triangulated.TensorHomGenerator

/-!
# Morphisms of `Dᵇ_fd` under a field extension

Let `F ⊆ F'` be a field extension. For `X`, `Y` in `Dᵇ_fd(F)`, extension of scalars induces a
bijection `F' ⊗_F Hom(X, Y) ≃ Hom(X_{F'}, Y_{F'})`
(`ModuleCat.tensorBijective_derivedExtendScalars`): by dévissage
(`CategoryTheory.Functor.tensorBijective_of_generator`) this reduces to `X = Y = F[0]` up to
shifts. Consequently extension of scalars is faithful on `Dᵇ_fd(F)`, and every morphism
`X_{F'} ⟶ Y_{F'}` is a finite `F'`-linear combination of extensions of morphisms `X ⟶ Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits DerivedCategory

open scoped TensorProduct

namespace ModuleCat

variable {F F' : Type (u + 1)} [Field F] [Field F'] [Algebra F F']

lemma flat_algebraMap_field : (algebraMap F F').Flat :=
  RingHom.flat_algebraMap_iff.2 inferInstance

variable (F F') in
/-- The extension of scalars `D(F) ⥤ D(F')` along a field extension. -/
noncomputable abbrev fieldExtendScalars :
    DerivedCategory (ModuleCat.{u + 1} F) ⥤ DerivedCategory (ModuleCat.{u + 1} F') :=
  derivedExtendScalars (algebraMap F F') flat_algebraMap_field

lemma fieldExtendScalars_map_smul (c : F) {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (f : X ⟶ Y) :
    (fieldExtendScalars F F').map (c • f) =
      algebraMap F F' c • (fieldExtendScalars F F').map f := by
  rw [show c • f = (c • 𝟙 X) ≫ f by rw [Linear.smul_comp, Category.id_comp], Functor.map_comp,
    derivedExtendScalars_map_smul_id, Linear.smul_comp, Category.id_comp]

/-- `F[0]`. -/
private noncomputable abbrev unitF (F : Type (u + 1)) [Field F] :
    DerivedCategory (ModuleCat.{u + 1} F) :=
  (singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)

private lemma exists_eq_smul_id_unitF (g : unitF F ⟶ unitF F) : ∃ c : F, g = c • 𝟙 _ :=
  exists_eq_smul_id_singleFunctor (1 : F) (fun v ↦ ⟨v, by simp⟩) g

private lemma eq_zero_of_smul_id_unitF {c : F} (h : c • 𝟙 (unitF F) = 0) : c = 0 :=
  eq_zero_of_smul_id_singleFunctor_eq_zero (1 : F) LinearMap.id rfl h

private lemma tensorBijective_unitF :
    (fieldExtendScalars F F').TensorBijective fieldExtendScalars_map_smul (unitF F) (unitF F) := by
  let e := derivedExtendScalarsSingleIso (algebraMap F F') flat_algebraMap_field
  have hend (g : (fieldExtendScalars F F').obj (unitF F) ⟶
      (fieldExtendScalars F F').obj (unitF F)) : ∃ a : F', g = a • 𝟙 _ := by
    obtain ⟨a, ha⟩ := exists_eq_smul_id_unitF (e.inv ≫ g ≫ e.hom)
    refine ⟨a, ?_⟩
    rw [← Rationalization.smul_id_conj e.symm, Iso.symm_inv, Iso.symm_hom, ← ha]
    simp
  have hpure (t : F' ⊗[F] (unitF F ⟶ unitF F)) : ∃ a : F', t = a ⊗ₜ 𝟙 _ := by
    induction t using TensorProduct.inductionOn with
    | tmul a f =>
      obtain ⟨c, rfl⟩ := exists_eq_smul_id_unitF f
      exact ⟨c • a, by rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [TensorProduct.add_tmul]⟩
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hpure t
    rw [Functor.tensorHom_tmul, CategoryTheory.Functor.map_id] at ht
    have : a • 𝟙 ((singleFunctor (ModuleCat.{u + 1} F') 0).obj (ModuleCat.of F' F')) = 0 := by
      rw [← Rationalization.smul_id_conj e, ht, Limits.zero_comp, Limits.comp_zero]
    rw [eq_zero_of_smul_id_singleFunctor_eq_zero (1 : F') LinearMap.id rfl this,
      TensorProduct.zero_tmul]
  · obtain ⟨a, rfl⟩ := hend g
    exact ⟨a ⊗ₜ 𝟙 _, by rw [Functor.tensorHom_tmul, CategoryTheory.Functor.map_id]⟩

private lemma tensorBijectiveShifts_unitF :
    (fieldExtendScalars F F').TensorBijectiveShifts fieldExtendScalars_map_smul
      (unitF F) (unitF F) := by
  refine Functor.tensorBijectiveShifts_of_forall fun n ↦ ?_
  by_cases hn : n = 0
  · subst hn
    exact tensorBijective_unitF.of_iso (Iso.refl _) ((shiftFunctorZero _ ℤ).app _).symm
  · have : Subsingleton (unitF F ⟶ (unitF F)⟦n⟧) :=
      ⟨fun f g ↦ by rw [eq_zero_of_singleFunctor_shift _ _ hn f,
        eq_zero_of_singleFunctor_shift _ _ hn g]⟩
    let e := derivedExtendScalarsSingleIso (algebraMap F F') flat_algebraMap_field
    have : Subsingleton ((fieldExtendScalars F F').obj (unitF F) ⟶
        (fieldExtendScalars F F').obj ((unitF F)⟦n⟧)) := ⟨fun f g ↦ by
      have h (f : (fieldExtendScalars F F').obj (unitF F) ⟶
          (fieldExtendScalars F F').obj ((unitF F)⟦n⟧)) : f = 0 := by
        rw [← cancel_epi e.inv, Limits.comp_zero,
          ← cancel_mono (((fieldExtendScalars F F').commShiftIso n).hom.app _ ≫ e.hom⟦n⟧'),
          Limits.zero_comp]
        exact eq_zero_of_singleFunctor_shift _ _ hn _
      rw [h f, h g]⟩
    exact Functor.TensorBijective.of_subsingleton

/-- Blueprint `lemma-perfect-complexes-geometric-point` (auxiliary): for a field extension `F ⊆ F'`
and `X`, `Y` in `Dᵇ_fd(F)`, extension of scalars induces
`F' ⊗_F Hom(X, Y) ≃ Hom(X_{F'}, Y_{F'})`. -/
theorem tensorBijective_fieldExtendScalars {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (hX : boundedFiniteCohomology F X) (hY : boundedFiniteCohomology F Y) :
    (fieldExtendScalars F F').TensorBijective fieldExtendScalars_map_smul X Y :=
  Functor.tensorBijective_of_generator (S := boundedFiniteCohomology F)
    (fun P _ _ hP _ hX ↦ prop_of_boundedFiniteCohomology P hP hX) tensorBijectiveShifts_unitF
    hX hY

/-- Extension of scalars along a field extension is faithful on `Dᵇ_fd`. -/
lemma fieldExtendScalars_map_injective {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (hX : boundedFiniteCohomology F X) (hY : boundedFiniteCohomology F Y) :
    Function.Injective ((fieldExtendScalars F F').map : (X ⟶ Y) → _) := by
  intro f g h
  apply Module.Flat.tensorProduct_mk_injective (R := F) (S := F') (M := X ⟶ Y)
  apply (tensorBijective_fieldExtendScalars (F' := F') hX hY).1
  simpa using h

/-- Every morphism `X_{F'} ⟶ Y_{F'}` between extensions of objects of `Dᵇ_fd(F)` is a finite
`F'`-linear combination of extensions of morphisms `X ⟶ Y`. -/
lemma exists_eq_sum_smul_fieldExtendScalars_map {X Y : DerivedCategory (ModuleCat.{u + 1} F)}
    (hX : boundedFiniteCohomology F X) (hY : boundedFiniteCohomology F Y)
    (g : (fieldExtendScalars F F').obj X ⟶ (fieldExtendScalars F F').obj Y) :
    ∃ s : Finset (F' × (X ⟶ Y)), g = ∑ p ∈ s, p.1 • (fieldExtendScalars F F').map p.2 := by
  obtain ⟨t, rfl⟩ := (tensorBijective_fieldExtendScalars (F' := F') hX hY).2 g
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  exact ⟨s, by simp⟩

section RingHom

variable {K K' : Type (u + 1)} [Field K] [Field K'] (φ : K →+* K') (hφ : φ.Flat)

/-- `ModuleCat.fieldExtendScalars_map_injective` for a ring morphism of fields. -/
lemma derivedExtendScalars_map_injective_of_field {X Y : DerivedCategory (ModuleCat.{u + 1} K)}
    (hX : boundedFiniteCohomology K X) (hY : boundedFiniteCohomology K Y) :
    Function.Injective ((derivedExtendScalars φ hφ).map : (X ⟶ Y) → _) :=
  letI := φ.toAlgebra
  fieldExtendScalars_map_injective (F' := K') hX hY

/-- `ModuleCat.exists_eq_sum_smul_fieldExtendScalars_map` for a ring morphism of fields. -/
lemma exists_eq_sum_smul_derivedExtendScalars_map_of_field
    {X Y : DerivedCategory (ModuleCat.{u + 1} K)}
    (hX : boundedFiniteCohomology K X) (hY : boundedFiniteCohomology K Y)
    (g : (derivedExtendScalars φ hφ).obj X ⟶ (derivedExtendScalars φ hφ).obj Y) :
    ∃ s : Finset (K' × (X ⟶ Y)), g = ∑ p ∈ s, p.1 • (derivedExtendScalars φ hφ).map p.2 :=
  letI := φ.toAlgebra
  exists_eq_sum_smul_fieldExtendScalars_map hX hY g

end RingHom

end ModuleCat
