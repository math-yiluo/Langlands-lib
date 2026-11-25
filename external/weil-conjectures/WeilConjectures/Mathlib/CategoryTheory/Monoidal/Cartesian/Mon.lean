/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Products and powers of morphisms of monoid objects

In a cartesian monoidal category, the morphisms `M ⟶ N` into a monoid object form a monoid
(`CategoryTheory.MonObj.Hom.monoid`). If `N` is commutative, the morphisms of monoid objects
form a submonoid: the unit is a morphism of monoid objects, and so are products and powers of
morphisms of monoid objects. In particular the `n`-th power `𝟙 M ^ n` of the identity of a
commutative monoid object, the "multiplication by `n`" map, is a morphism of monoid objects.

## Main statements

- `CategoryTheory.MonObj.isMonHom_pow`: a power of a morphism of monoid objects into a
  commutative monoid object is a morphism of monoid objects.
- `CategoryTheory.MonObj.id_pow_comp_id_pow`: `𝟙 M ^ m ≫ 𝟙 M ^ n = 𝟙 M ^ (m * n)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.MonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

/-- Composing the multiplication-by-`m` and multiplication-by-`n` maps of a monoid object gives
multiplication by `m * n`. -/
@[to_additive /-- Composing the multiplication-by-`m` and multiplication-by-`n` maps of an
additive monoid object gives multiplication by `m * n`. -/]
lemma id_pow_comp_id_pow (M : C) [MonObj M] (m n : ℕ) :
    (𝟙 M ^ m) ≫ (𝟙 M ^ n) = 𝟙 M ^ (m * n) := by
  rw [comp_pow, Category.comp_id, pow_mul]

variable [BraidedCategory C] {M N : C} [MonObj M] [MonObj N] [IsCommMonObj N]

/-- The unit `1 : M ⟶ N` into a commutative monoid object is a morphism of monoid objects. -/
@[to_additive /-- The zero `0 : M ⟶ N` into a commutative additive monoid object is a morphism
of additive monoid objects. -/]
instance isMonHom_one : IsMonHom (1 : M ⟶ N) := by
  rw [Hom.one_def]
  infer_instance

/-- The product of two morphisms of monoid objects into a commutative monoid object is a
morphism of monoid objects. -/
@[to_additive /-- The sum of two morphisms of additive monoid objects into a commutative
additive monoid object is a morphism of additive monoid objects. -/]
instance isMonHom_mul (f g : M ⟶ N) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

/-- Blueprint `definition-abelian-variety`: multiplication by `n` is a homomorphism.

A power `f ^ n` of a morphism of monoid objects into a commutative monoid object is a morphism
of monoid objects. Applied to `f = 𝟙 M` this says that the `n`-fold product `𝟙 M ^ n`, which
on `X`-points is `x ↦ x ^ n` (`CategoryTheory.MonObj.comp_pow`), is a homomorphism. -/
@[to_additive /-- A multiple `n • f` of a morphism of additive monoid objects into a commutative
additive monoid object is a morphism of additive monoid objects. -/]
instance isMonHom_pow (f : M ⟶ N) [IsMonHom f] (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; infer_instance
  | succ n ih => rw [pow_succ]; infer_instance

end CategoryTheory.MonObj
