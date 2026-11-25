/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap

/-!
# The `Hom` groups of the rationalization

Let `M` be a submonoid of a commutative ring `R`, `C` an `R`-linear triangulated category and
`A` a localization of `R` at `M`. This file identifies the morphisms of the rationalization
`Rationalization M C` between objects of `C` with the localizations of the `Hom` groups of `C`:
the `R`-linear map `(X ⟶ Y) → (Q X ⟶ Q Y)` induced by the localization functor `Q` is a
localization of `R`-modules at `M`, hence a base change from `R` to `A`.

## Main results

- `CategoryTheory.Rationalization.isLocalizedModule_mapLinearMap` : the map
  `(X ⟶ Y) →ₗ[R] (Q X ⟶ Q Y)` is a localization at `M`.
- `CategoryTheory.Rationalization.tensorHomEquiv` : the `A`-linear equivalence
  `A ⊗[R] (X ⟶ Y) ≃ₗ[A] (Q X ⟶ Q Y)`, sending `a ⊗ f` to `a • Q f`.
- `CategoryTheory.Rationalization.exists_iso_obj` : every object of the rationalization is
  isomorphic to `Q X` for some object `X` of `C` (a *lattice*).
- `CategoryTheory.Rationalization.exists_pow_smul_eq_map`,
  `CategoryTheory.Rationalization.exists_eq_inv_pow_smul_map` : clearing denominators, when
  every element of `M` divides a power of a fixed `ϖ`: every morphism `Q X ⟶ Q Y` is of the
  form `ϖ⁻ᴺ • Q u`.
- `CategoryTheory.Rationalization.functor_linear`, `CategoryTheory.Rationalization.linear_map` :
  `R`-linear functors between rationalizations, in particular those induced by `R`-linear
  triangulated functors, are `A`-linear.
- `CategoryTheory.Rationalization.isEquivalence_toKaroubi` : if the rationalization is
  idempotent complete, it is equivalent to its Karoubi envelope.
-/

@[expose] public section

universe w' w v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Pretriangulated TensorProduct

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R]
  [Pretriangulated D] [IsTriangulated D]

section Hom

/-- The `Hom` groups of the rationalization between objects of `C` are the localizations at `M`
of the `Hom` groups of `C`: the `R`-linear map induced by the localization functor is a
localization of `R`-modules. -/
instance isLocalizedModule_mapLinearMap (X Y : C) :
    IsLocalizedModule M ((Q M C).mapLinearMap R (X := X) (Y := Y)) where
  map_units m := by
    rw [Module.End.isUnit_iff]
    refine ⟨smul_left_injective m.2, fun φ ↦ ?_⟩
    have := isIso_smul_id m.2 ((Q M C).obj X)
    refine ⟨inv ((m : R) • 𝟙 ((Q M C).obj X)) ≫ φ, ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [← Linear.smul_comp, ← id_comp (inv _), ← Linear.smul_comp, assoc,
      IsIso.hom_inv_id_assoc]
  surj φ := by
    obtain ⟨m, hm, f, h⟩ := exists_smul_eq_map φ
    exact ⟨⟨f, ⟨m, hm⟩⟩, h⟩
  exists_of_eq {f g} h := by
    obtain ⟨m, hm, h'⟩ := (map_eq_map_iff f g).1 h
    exact ⟨⟨m, hm⟩, h'⟩

variable (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]

/-- The `A`-linear structure of the rationalization is compatible with its `R`-linear
structure. -/
instance isScalarTower_hom (X Y : Rationalization M C) : IsScalarTower R A (X ⟶ Y) where
  smul_assoc r a f := by
    rw [Algebra.smul_def, mul_smul, algebraMap_smul]

/-- The `Hom` groups of the rationalization between objects of `C` are obtained from those of
`C` by extension of scalars from `R` to a localization `A` of `R` at `M`. -/
lemma isBaseChange_mapLinearMap (X Y : C) :
    IsBaseChange A ((Q M C).mapLinearMap R (X := X) (Y := Y)) :=
  IsLocalizedModule.isBaseChange M A _

/-- The `A`-linear equivalence `A ⊗[R] (X ⟶ Y) ≃ (Q X ⟶ Q Y)`, sending `a ⊗ f` to `a • Q f`:
the morphisms of the rationalization are those of `C` tensored up to `A`. -/
noncomputable def tensorHomEquiv (X Y : C) :
    A ⊗[R] (X ⟶ Y) ≃ₗ[A] ((Q M C).obj X ⟶ (Q M C).obj Y) :=
  (isBaseChange_mapLinearMap M A X Y).equiv

@[simp]
lemma tensorHomEquiv_tmul {X Y : C} (a : A) (f : X ⟶ Y) :
    tensorHomEquiv M A X Y (a ⊗ₜ f) = a • (Q M C).map f :=
  (isBaseChange_mapLinearMap M A X Y).equiv_tmul a f

/-- Multiplying the fraction `r / m` of `A` by `m` gives `r`, also on morphisms of the
rationalization. -/
lemma smul_mk'_smul {X Y : Rationalization M C} (r : R) (m : M)
    (f : X ⟶ Y) : (m : R) • IsLocalization.mk' A r m • f = r • f := by
  rw [← algebraMap_smul A, ← algebraMap_smul A, smul_smul, IsLocalization.mk'_spec']

/-- An `R`-linear functor between rationalizations is linear over any localization `A` of `R`
at `M`. -/
lemma functor_linear (G : Rationalization M C ⥤ Rationalization M D)
    [G.Linear R] : G.Linear A where
  map_smul {X Y} f a := by
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M a
    refine smul_left_injective m.2 ?_
    dsimp only
    rw [← Functor.map_smul, smul_mk'_smul, smul_mk'_smul, Functor.map_smul]

/-- The functor induced on rationalizations by an `R`-linear triangulated functor is linear
over any localization `A` of `R` at `M`. -/
instance linear_map (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    (map M F).Linear A :=
  functor_linear M A _

end Hom

variable {M}

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C] in
/-- Every object of the rationalization is isomorphic to the image of an object of `C`: every
rational object has a lattice. -/
lemma exists_iso_obj (Y : Rationalization M C) : ∃ X : C, Nonempty ((Q M C).obj X ≅ Y) :=
  ⟨_, ⟨(Q M C).objObjPreimageIso Y⟩⟩

/-- Clearing denominators: if every element of `M` divides a power of `ϖ`, then every morphism
of the rationalization between objects of `C` becomes the image of a morphism of `C` after
multiplication by a power of `ϖ`. -/
lemma exists_pow_smul_eq_map {ϖ : R} (hϖ : ∀ m ∈ M, ∃ (N : ℕ) (a : R), m * a = ϖ ^ N)
    {X Y : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
    ∃ (N : ℕ) (u : X ⟶ Y), ϖ ^ N • φ = (Q M C).map u := by
  obtain ⟨m, hm, f, h⟩ := exists_smul_eq_map φ
  obtain ⟨N, a, ha⟩ := hϖ m hm
  refine ⟨N, a • f, ?_⟩
  rw [← ha, mul_comm, mul_smul, h, Functor.map_smul]

/-- Clearing denominators, over a field `A` which is a localization of `R` at `M`: if `ϖ ∈ M`
and every element of `M` divides a power of `ϖ`, then every morphism of the rationalization
between objects of `C` is of the form `ϖ⁻ᴺ • Q u`. -/
lemma exists_eq_inv_pow_smul_map (A : Type w') [Field A] [Algebra R A] [IsLocalization M A]
    {ϖ : R} (hϖM : ϖ ∈ M) (hϖ : ∀ m ∈ M, ∃ (N : ℕ) (a : R), m * a = ϖ ^ N)
    {X Y : C} (φ : (Q M C).obj X ⟶ (Q M C).obj Y) :
    ∃ (N : ℕ) (u : X ⟶ Y), φ = (algebraMap R A ϖ)⁻¹ ^ N • (Q M C).map u := by
  obtain ⟨N, u, h⟩ := exists_pow_smul_eq_map hϖ φ
  refine ⟨N, u, ?_⟩
  have hne : algebraMap R A ϖ ≠ 0 := (IsLocalization.map_units A ⟨ϖ, hϖM⟩).ne_zero
  rw [← h, ← algebraMap_smul A, smul_smul, map_pow, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hne),
    one_smul]

/-- An idempotent complete category `C'` (for instance the rationalization, or a full
subcategory of it, when it is idempotent complete) is equivalent to its Karoubi envelope through
the canonical functor. -/
lemma isEquivalence_toKaroubi (C' : Type*) [Category C'] [IsIdempotentComplete C'] :
    (Idempotents.toKaroubi C').IsEquivalence :=
  inferInstance

end CategoryTheory.Rationalization
