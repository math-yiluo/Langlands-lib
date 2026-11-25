/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Conv
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!

# Convolution rings and ring objects in monoidal categories

Let `(C, ⊗, 𝟙)` be a monoidal category. An *(associative unital) algebra object* in `C` is an
object `R` with a multiplication `μ : R ⊗ R ⟶ R` and a unit `η : 𝟙 ⟶ R` which are associative
and unital up to the associativity and unit constraints of `C`. In Mathlib these are the
instances `[MonObj R]`, and the category they form is `Mon C`, written `Alg(C)` in the
literature. No additive structure is required for this definition. When `C` is braided,
`R` is *commutative* if `μ = β_{R,R} ≫ μ`, which is the predicate `[IsCommMonObj R]`; these form
the category `CommMon C`, written `CAlg(C)`.

When `C` is preadditive and the tensor product is additive in each variable
(`MonoidalPreadditive C`), algebra objects deserve the name *ring objects*: the morphisms
from a comonoid object to a ring object form a ring for the convolution product
(`Conv.instRing`). In particular, for an algebra object `R`, the *global sections*
`Γ R = 𝟙 ⟶ R` form a ring (`MonObj.Γ`), which is commutative when `R` is.

## Main definitions

* `CategoryTheory.Conv.instRing`: the convolution ring `Conv M N`, for a comonoid object `M` and
  a monoid object `N` in a monoidal preadditive category.
* `CategoryTheory.MonObj.Γ`: the ring of global sections `𝟙_ C ⟶ R` of an algebra object `R`.
* `CategoryTheory.MonObj.Γ.map`: the ring homomorphism `Γ R →+* Γ S` induced by a morphism
  of algebra objects.
* `CategoryTheory.MonObj.Γ.mapFunctor`: the ring homomorphism `Γ R →+* Γ (F R)` induced by a
  lax monoidal additive functor `F`.

-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj ComonObj Preadditive Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Conv

/-- The underlying morphism of an element of the convolution monoid. -/
def toHom {M N : C} (f : Conv M N) : M ⟶ N := f

omit [MonoidalCategory C] in
lemma toHom_injective {M N : C} : Function.Injective (toHom : Conv M N → (M ⟶ N)) :=
  fun _ _ h ↦ h

lemma toHom_mul {M N : C} [ComonObj M] [MonObj N] (f g : Conv M N) :
    toHom (f * g) = Δ[M] ≫ toHom f ▷ M ≫ N ◁ toHom g ≫ μ[N] :=
  rfl

lemma toHom_one {M N : C} [ComonObj M] [MonObj N] : toHom (1 : Conv M N) = ε[M] ≫ η[N] :=
  rfl


section Preadditive

variable [Preadditive C] {M N : C}

instance : AddCommGroup (Conv M N) := inferInstanceAs (AddCommGroup (M ⟶ N))

omit [MonoidalCategory C] in
lemma toHom_add (f g : Conv M N) : toHom (f + g) = toHom f + toHom g := rfl

omit [MonoidalCategory C] in
lemma toHom_zero : toHom (0 : Conv M N) = 0 := rfl

variable [MonoidalPreadditive C] [ComonObj M] [MonObj N]

/-- The convolution product on morphisms from a comonoid object to a monoid object in a
monoidal preadditive category is distributive, so that these morphisms form a ring. -/
instance instRing : Ring (Conv M N) where
  __ := (inferInstance : Monoid (Conv M N))
  __ := (inferInstance : AddCommGroup (Conv M N))
  left_distrib f g h := toHom_injective (by
    simp only [toHom_mul, toHom_add, MonoidalPreadditive.whiskerLeft_add, add_comp, comp_add])
  right_distrib f g h := toHom_injective (by
    simp only [toHom_mul, toHom_add, MonoidalPreadditive.add_whiskerRight, add_comp, comp_add])
  zero_mul f := toHom_injective (by
    simp only [toHom_mul, toHom_zero, MonoidalPreadditive.zero_whiskerRight, zero_comp,
      comp_zero])
  mul_zero f := toHom_injective (by
    simp only [toHom_mul, toHom_zero, MonoidalPreadditive.whiskerLeft_zero, zero_comp,
      comp_zero])

end Preadditive

end Conv

namespace MonObj

attribute [local instance] ComonObj.instTensorUnit

/-- The global sections `𝟙_ C ⟶ R` of an algebra object `R`. When `C` is monoidal preadditive,
this is a ring for the convolution product `f * g = λ⁻¹ ≫ (f ⊗ g) ≫ μ`. -/
def Γ (R : C) [MonObj R] : Type v := Conv (𝟙_ C) R

namespace Γ

variable {R : C} [MonObj R]

instance : Monoid (Γ R) := inferInstanceAs (Monoid (Conv (𝟙_ C) R))

/-- The underlying morphism of a global section. -/
def hom (f : Γ R) : 𝟙_ C ⟶ R := Conv.toHom f

/-- A morphism `𝟙_ C ⟶ R`, as a global section. -/
def ofHom (f : 𝟙_ C ⟶ R) : Γ R := f

@[simp] lemma hom_ofHom (f : 𝟙_ C ⟶ R) : (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom (f : Γ R) : ofHom f.hom = f := rfl

@[ext] lemma ext {f g : Γ R} (h : f.hom = g.hom) : f = g := h

@[simp] lemma one_hom : (1 : Γ R).hom = η[R] := Category.id_comp _

lemma mul_hom (f g : Γ R) : (f * g).hom = (λ_ (𝟙_ C)).inv ≫ (f.hom ⊗ₘ g.hom) ≫ μ[R] :=
  (Conv.toHom_mul (M := 𝟙_ C) (N := R) f g).trans (by
    rw [tensorHom_def, Category.assoc]
    rfl)

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

instance : Ring (Γ R) := inferInstanceAs (Ring (Conv (𝟙_ C) R))

@[simp] lemma add_hom (f g : Γ R) : (f + g).hom = f.hom + g.hom := rfl

@[simp] lemma zero_hom : (0 : Γ R).hom = 0 := rfl

@[simp] lemma neg_hom (f : Γ R) : (-f).hom = -f.hom := rfl

variable [BraidedCategory C] [IsCommMonObj R]

lemma mul_comm' (f g : Γ R) : f * g = g * f := by
  ext
  rw [mul_hom, mul_hom]
  conv_rhs => rw [← IsCommMonObj.mul_comm R, BraidedCategory.braiding_naturality_assoc,
    leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]

/-- The global sections of a commutative algebra object form a commutative ring. -/
instance : CommRing (Γ R) where
  mul_comm := mul_comm'

end Preadditive

end Γ

section Map

variable {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- A morphism of algebra objects induces a monoid homomorphism on global sections. -/
def Γ.mapMonoidHom : Γ R →* Γ S where
  toFun f := Γ.ofHom (f.hom ≫ φ)
  map_one' := by ext; simp
  map_mul' f g := by
    ext
    simp only [Γ.mul_hom, hom_ofHom, Category.assoc]
    rw [IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

variable [Preadditive C] [MonoidalPreadditive C]

/-- A morphism of algebra objects induces a ring homomorphism on global sections. -/
def Γ.map : Γ R →+* Γ S where
  __ := Γ.mapMonoidHom φ
  map_zero' := by ext; simp [Γ.mapMonoidHom]
  map_add' f g := by ext; simp [Γ.mapMonoidHom]

@[simp] lemma Γ.map_hom (f : Γ R) : (Γ.map φ f).hom = f.hom ≫ φ := rfl

end Map

section MapFunctor

/-!
### Global sections under lax monoidal functors

A lax monoidal functor `F : C ⥤ D` sends an algebra object `R` to the algebra object `F R`
(`Functor.monObjObj`), and a global section `s : 𝟙 ⟶ R` to the global section
`ε ≫ F s : 𝟙 ⟶ F R`. This is a monoid homomorphism `Γ R →* Γ (F R)`, and a ring
homomorphism when `F` is additive.
-/

open Functor.LaxMonoidal

open scoped Obj

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
  {R : C} [MonObj R]

/-- A lax monoidal functor induces a monoid homomorphism on global sections. -/
def Γ.mapFunctorMonoidHom : Γ R →* Γ (F.obj R) where
  toFun s := Γ.ofHom (Functor.LaxMonoidal.ε F ≫ F.map s.hom)
  map_one' := by ext; simp
  map_mul' s t := by
    have h : Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ C)).inv = (λ_ (𝟙_ D)).inv ≫
        (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫ Functor.LaxMonoidal.μ F _ _ := by
      rw [tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc, left_unitality_inv]
    ext
    simp only [Γ.hom_ofHom, Γ.mul_hom, F.map_comp, Functor.obj.μ_def]
    rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, reassoc_of% h]

@[simp]
lemma Γ.mapFunctorMonoidHom_hom (s : Γ R) :
    (Γ.mapFunctorMonoidHom F s).hom = Functor.LaxMonoidal.ε F ≫ F.map s.hom :=
  rfl

variable [Preadditive C] [MonoidalPreadditive C] [Preadditive D] [MonoidalPreadditive D]
  [F.Additive]

/-- A lax monoidal additive functor induces a ring homomorphism on global sections. -/
def Γ.mapFunctor : Γ R →+* Γ (F.obj R) where
  __ := Γ.mapFunctorMonoidHom F
  map_zero' := by ext; simp [Γ.mapFunctorMonoidHom]
  map_add' s t := by ext; simp [Γ.mapFunctorMonoidHom]

@[simp]
lemma Γ.mapFunctor_hom (s : Γ R) :
    (Γ.mapFunctor F s).hom = Functor.LaxMonoidal.ε F ≫ F.map s.hom :=
  rfl

end MapFunctor

end MonObj

end CategoryTheory
