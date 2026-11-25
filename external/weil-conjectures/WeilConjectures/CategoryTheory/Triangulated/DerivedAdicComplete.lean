/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Derived adic completeness

Let `C` be a preadditive category, `K : C` an object with a countable product
`P = ∏_{i : ℕ} K`, and `n : ℤ`. Let `s : P ⟶ P` be the shift with `s ≫ π_i = π_{i+1}`.
By Milnor's description of derived limits, the derived limit of the tower
`⋯ --n--> K --n--> K` is the fibre of `𝟙 - n • s : P ⟶ P`. Hence `K` is *derived
`n`-adically complete* (i.e. `R lim (⋯ --n--> K --n--> K) = 0`, see Stacks 091N, 091Q) if and
only if `𝟙 - n • s` is an isomorphism. We take this as a purely categorical definition.

## Main definitions

- `CategoryTheory.adicTowerShift`: the shift `s : ∏ᵢ K ⟶ ∏ᵢ K`.
- `CategoryTheory.IsDerivedAdicComplete`: `K` is derived `n`-adically complete if
  `𝟙 - n • adicTowerShift K` is an isomorphism.
- `CategoryTheory.isDerivedAdicComplete`: the corresponding `ObjectProperty`.
- `CategoryTheory.powerTriangleOneSubZSMulAdicTowerShift`: `𝟙 - n • adicTowerShift` as an
  endomorphism of the countable power `CategoryTheory.powerTriangle T` of a triangle.

## Main statements

- `CategoryTheory.IsDerivedAdicComplete.isZero_of_isIso_zsmul_id`: derived Nakayama: if `K` is
  derived `n`-adically complete and `n` acts invertibly on `K`, then `K` is zero.
- `CategoryTheory.IsDerivedAdicComplete.map`: preservation by additive functors preserving the
  relevant countable product.
- `CategoryTheory.IsDerivedAdicComplete.of_distTriang₁₂` (and variants): two out of three for
  distinguished triangles in a pretriangulated category.
- `CategoryTheory.IsDerivedAdicComplete.shift`: stability under shifts.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Preadditive

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Shift

variable (K : C) [HasProduct (fun _ : ℕ ↦ K)]

/-- The shift endomorphism `s` of `∏_{i : ℕ} K`, characterised by `s ≫ π_i = π_{i+1}`. -/
noncomputable def adicTowerShift : ∏ᶜ (fun _ : ℕ ↦ K) ⟶ ∏ᶜ (fun _ : ℕ ↦ K) :=
  Pi.lift fun i ↦ Pi.π _ (i + 1)

/-- The defining property of `adicTowerShift`: `s ≫ π_i = π_{i+1}`. -/
@[reassoc (attr := simp)]
lemma adicTowerShift_π (i : ℕ) :
    adicTowerShift K ≫ Pi.π (fun _ : ℕ ↦ K) i = Pi.π (fun _ : ℕ ↦ K) (i + 1) := by
  simp [adicTowerShift]

end Shift

section Preadditive

variable [Preadditive C]

/-- An object `K` is *derived `n`-adically complete* if `𝟙 - n • s` is an isomorphism, where
`s` is the shift endomorphism of `∏_{i : ℕ} K`. Equivalently, the derived limit of the tower
`⋯ --n--> K --n--> K` vanishes. -/
@[stacks 091N]
def IsDerivedAdicComplete (n : ℤ) (K : C) [HasProduct (fun _ : ℕ ↦ K)] : Prop :=
  IsIso (𝟙 _ - n • adicTowerShift K)

/-- Naturality of `𝟙 - n • adicTowerShift` with respect to morphisms `K ⟶ L`. -/
@[reassoc]
lemma pi_map_comp_one_sub_zsmul_adicTowerShift (n : ℤ) {K L : C} (f : K ⟶ L)
    [HasProduct (fun _ : ℕ ↦ K)] [HasProduct (fun _ : ℕ ↦ L)] :
    Limits.Pi.map (fun _ ↦ f) ≫ (𝟙 _ - n • adicTowerShift L) =
      (𝟙 _ - n • adicTowerShift K) ≫ Limits.Pi.map (fun _ ↦ f) := by
  ext i
  simp [sub_comp, comp_sub]

/-- The image of `𝟙 - n • adicTowerShift K` under an additive functor `F`, composed with the
comparison map `F.obj (∏ K) ⟶ ∏ F.obj K`, agrees with `𝟙 - n • adicTowerShift (F.obj K)`. -/
@[reassoc]
lemma map_one_sub_zsmul_adicTowerShift_comp_piComparison [Preadditive D] (F : C ⥤ D)
    [F.Additive] (n : ℤ) (K : C) [HasProduct (fun _ : ℕ ↦ K)]
    [HasProduct (fun _ : ℕ ↦ F.obj K)] :
    F.map (𝟙 _ - n • adicTowerShift K) ≫ piComparison F (fun _ : ℕ ↦ K) =
      piComparison F (fun _ : ℕ ↦ K) ≫ (𝟙 _ - n • adicTowerShift (F.obj K)) := by
  ext i
  simp [F.map_sub, F.map_zsmul, sub_comp, comp_sub, ← F.map_comp]

namespace IsDerivedAdicComplete

/-- Derived `n`-adic completeness is invariant under isomorphisms. -/
lemma of_iso {n : ℤ} {K L : C} [HasProduct (fun _ : ℕ ↦ K)] [HasProduct (fun _ : ℕ ↦ L)]
    (hK : IsDerivedAdicComplete n K) (e : K ≅ L) : IsDerivedAdicComplete n L := by
  obtain ⟨E, hE⟩ : ∃ E : ∏ᶜ (fun _ : ℕ ↦ K) ≅ ∏ᶜ (fun _ : ℕ ↦ L),
      E.hom = Limits.Pi.map fun _ ↦ e.hom :=
    ⟨{ hom := Limits.Pi.map fun _ ↦ e.hom
       inv := Limits.Pi.map fun _ ↦ e.inv }, rfl⟩
  have h : 𝟙 _ - n • adicTowerShift L = E.inv ≫ (𝟙 _ - n • adicTowerShift K) ≫ E.hom := by
    rw [Iso.eq_inv_comp, hE]
    exact pi_map_comp_one_sub_zsmul_adicTowerShift n e.hom
  have : IsIso (𝟙 _ - n • adicTowerShift K) := hK
  rw [IsDerivedAdicComplete, h]
  infer_instance

/-- **Derived Nakayama**: if `K` is derived `n`-adically complete and multiplication by `n`
is an isomorphism on `K`, then `K` is zero. -/
lemma isZero_of_isIso_zsmul_id {n : ℤ} {K : C} [HasProduct (fun _ : ℕ ↦ K)]
    (hK : IsDerivedAdicComplete n K) (hn : IsIso (n • 𝟙 K)) : IsZero K := by
  have : IsIso (𝟙 _ - n • adicTowerShift K) := hK
  let u : End K := .of (inv (n • 𝟙 K))
  have hu : n • u.asHom = 𝟙 K := by
    change n • inv (n • 𝟙 K) = 𝟙 K
    conv_rhs => rw [← IsIso.hom_inv_id (n • 𝟙 K)]
    rw [zsmul_comp, id_comp]
  have hι : (Pi.lift fun i ↦ (u ^ i).asHom) ≫ (𝟙 _ - n • adicTowerShift K) =
      0 ≫ (𝟙 _ - n • adicTowerShift K) := by
    ext i
    simp only [assoc, sub_comp, id_comp, zsmul_comp, adicTowerShift_π, comp_sub, comp_zsmul,
      zero_comp, Pi.lift_comp_π, smul_zero, sub_zero]
    rw [pow_succ', End.mul_asHom, ← comp_zsmul, hu, comp_id, sub_self]
  rw [cancel_mono] at hι
  rw [IsZero.iff_id_eq_zero]
  simpa using congrArg (· ≫ Pi.π (fun _ : ℕ ↦ K) 0) hι

/-- Derived `n`-adic completeness is preserved by additive functors which preserve the
product `∏_{i : ℕ} K`. -/
lemma map [Preadditive D] (F : C ⥤ D) [F.Additive] {n : ℤ} {K : C}
    [HasProduct (fun _ : ℕ ↦ K)] [HasProduct (fun _ : ℕ ↦ F.obj K)]
    [PreservesLimit (Discrete.functor fun _ : ℕ ↦ K) F]
    (hK : IsDerivedAdicComplete n K) : IsDerivedAdicComplete n (F.obj K) := by
  have : IsIso (𝟙 _ - n • adicTowerShift K) := hK
  have h : 𝟙 _ - n • adicTowerShift (F.obj K) = (PreservesProduct.iso F _).inv ≫
      F.map (𝟙 _ - n • adicTowerShift K) ≫ (PreservesProduct.iso F _).hom := by
    rw [Iso.eq_inv_comp, PreservesProduct.iso_hom,
      map_one_sub_zsmul_adicTowerShift_comp_piComparison]
  rw [IsDerivedAdicComplete, h]
  infer_instance

/-- Derived `n`-adic completeness is preserved by additive functors which preserve countable
products indexed by `ℕ`. -/
lemma map' [Preadditive D] (F : C ⥤ D) [F.Additive] [HasCountableProducts C]
    [HasCountableProducts D] [PreservesLimitsOfShape (Discrete ℕ) F] {n : ℤ} {K : C}
    (hK : IsDerivedAdicComplete n K) : IsDerivedAdicComplete n (F.obj K) :=
  hK.map F

end IsDerivedAdicComplete

/-- The property of objects of being derived `n`-adically complete. -/
def isDerivedAdicComplete [HasCountableProducts C] (n : ℤ) : ObjectProperty C :=
  fun K ↦ IsDerivedAdicComplete n K

/-- Derived `n`-adic completeness is closed under isomorphisms. -/
instance [HasCountableProducts C] (n : ℤ) :
    (isDerivedAdicComplete (C := C) n).IsClosedUnderIsomorphisms where
  of_iso e hK := IsDerivedAdicComplete.of_iso hK e

end Preadditive

section Pretriangulated

open Pretriangulated

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [HasCountableProducts C]

/-- Derived `n`-adic completeness is stable under shifts. -/
lemma IsDerivedAdicComplete.shift {n : ℤ} {K : C} (hK : IsDerivedAdicComplete n K) (a : ℤ) :
    IsDerivedAdicComplete n (K⟦a⟧) :=
  hK.map (shiftFunctor C a)
/-- The countable power `∏_{i : ℕ} T` of a triangle `T`, i.e. `productTriangle` of the
constant family at `T`, written with objects `∏ᶜ fun _ : ℕ ↦ T.objᵢ`. -/
noncomputable def powerTriangle (T : Triangle C) : Triangle C :=
  Triangle.mk (Limits.Pi.map fun _ : ℕ ↦ T.mor₁) (Limits.Pi.map fun _ : ℕ ↦ T.mor₂)
    (Limits.Pi.map (fun _ : ℕ ↦ T.mor₃) ≫
      inv (piComparison (shiftFunctor C (1 : ℤ)) fun _ : ℕ ↦ T.obj₁))

/-- The endomorphism `𝟙 - n • adicTowerShift` of the countable power of a triangle `T`, as a
morphism of triangles. -/
noncomputable def powerTriangleOneSubZSMulAdicTowerShift (n : ℤ) (T : Triangle C) :
    powerTriangle T ⟶ powerTriangle T where
  hom₁ := 𝟙 _ - n • adicTowerShift T.obj₁
  hom₂ := 𝟙 _ - n • adicTowerShift T.obj₂
  hom₃ := 𝟙 _ - n • adicTowerShift T.obj₃
  comm₁ := pi_map_comp_one_sub_zsmul_adicTowerShift n T.mor₁
  comm₂ := pi_map_comp_one_sub_zsmul_adicTowerShift n T.mor₂
  comm₃ := by
    have h : (Limits.Pi.map (fun _ : ℕ ↦ T.mor₃) ≫
        inv (piComparison (shiftFunctor C (1 : ℤ)) fun _ : ℕ ↦ T.obj₁)) ≫
          (𝟙 _ - n • adicTowerShift T.obj₁)⟦(1 : ℤ)⟧' =
        (𝟙 _ - n • adicTowerShift T.obj₃) ≫ Limits.Pi.map (fun _ : ℕ ↦ T.mor₃) ≫
          inv (piComparison (shiftFunctor C (1 : ℤ)) fun _ : ℕ ↦ T.obj₁) := by
      rw [assoc, ← cancel_mono (piComparison _ _), assoc, assoc,
        map_one_sub_zsmul_adicTowerShift_comp_piComparison, IsIso.inv_hom_id_assoc, assoc,
        assoc, IsIso.inv_hom_id, comp_id, pi_map_comp_one_sub_zsmul_adicTowerShift]
    exact h

variable [HasZeroObject C] [Pretriangulated C]

/-- The countable power of a distinguished triangle is distinguished. -/
lemma powerTriangle_distinguished (T : Triangle C) (hT : T ∈ distTriang C) :
    powerTriangle T ∈ distTriang C :=
  productTriangle_distinguished (fun _ : ℕ ↦ T) fun _ ↦ hT

namespace IsDerivedAdicComplete

/-- In a distinguished triangle, if the first two objects are derived `n`-adically complete,
so is the third. -/
lemma of_distTriang₁₂ {n : ℤ} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsDerivedAdicComplete n T.obj₁) (h₂ : IsDerivedAdicComplete n T.obj₂) :
    IsDerivedAdicComplete n T.obj₃ :=
  isIso₃_of_isIso₁₂ (powerTriangleOneSubZSMulAdicTowerShift n T)
    (powerTriangle_distinguished T hT) (powerTriangle_distinguished T hT) h₁ h₂

/-- In a distinguished triangle, if the last two objects are derived `n`-adically complete,
so is the first. -/
lemma of_distTriang₂₃ {n : ℤ} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : IsDerivedAdicComplete n T.obj₂) (h₃ : IsDerivedAdicComplete n T.obj₃) :
    IsDerivedAdicComplete n T.obj₁ :=
  isIso₁_of_isIso₂₃ (powerTriangleOneSubZSMulAdicTowerShift n T)
    (powerTriangle_distinguished T hT) (powerTriangle_distinguished T hT) h₂ h₃

/-- In a distinguished triangle, if the first and third objects are derived `n`-adically
complete, so is the second. -/
lemma of_distTriang₁₃ {n : ℤ} (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsDerivedAdicComplete n T.obj₁) (h₃ : IsDerivedAdicComplete n T.obj₃) :
    IsDerivedAdicComplete n T.obj₂ :=
  isIso₂_of_isIso₁₃ (powerTriangleOneSubZSMulAdicTowerShift n T)
    (powerTriangle_distinguished T hT) (powerTriangle_distinguished T hT) h₁ h₃

end IsDerivedAdicComplete

end Pretriangulated

end CategoryTheory
