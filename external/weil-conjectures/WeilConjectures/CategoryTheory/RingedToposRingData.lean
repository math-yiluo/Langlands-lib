/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphism

/-!
# The ring data of a ringed geometric morphism

The geometric adjunction and its structural ring map, before constructing the induced
module direct image. Source: Stacks Project, Modules on Sites, ringed topoi and
pushforward of modules.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The geometric adjunction and structural ring map of `RingedToposMorphism`.
This contains no choice of a module direct image. -/
structure RingedToposMorphism.RingData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u}) where
  /-- Inverse image of sheaves of sets. -/
  inverse : Sheaf K (Type u) ⥤ Sheaf J (Type u)
  /-- Direct image of sheaves of sets. -/
  direct : Sheaf J (Type u) ⥤ Sheaf K (Type u)
  /-- The geometric adjunction. -/
  adj : inverse ⊣ direct
  /-- Left exactness is required only for the underlying inverse image. -/
  leftExact : PreservesFiniteLimits inverse
  /-- The structural map, with ring structure specified by generalized elements below. -/
  ringMap : inverse.obj ((sheafCompose K (forget RingCat)).obj B) ⟶
    (sheafCompose J (forget RingCat)).obj A
  /-- Preservation of zero. -/
  ring_zero : ∀ (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Zero.zero (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @Zero.zero (A.obj.obj U) inferInstance
  /-- Preservation of one. -/
  ring_one : ∀ (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @One.one (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @One.one (A.obj.obj U) inferInstance
  /-- Preservation of add. -/
  ring_add : ∀ (T : Sheaf K (Type u))
    (x y z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Add.add (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- Preservation of mul. -/
  ring_mul : ∀ (T : Sheaf K (Type u))
    (x y z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Mul.mul (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)

/-- Forget the induced module functor of a ringed-topos morphism. -/
def RingedToposMorphism.ringData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism A B) : RingedToposMorphism.RingData A B where
  inverse := f.inverse
  direct := f.direct
  adj := f.adj
  leftExact := f.leftExact
  ringMap := f.ringMap
  ring_zero := f.ring_zero
  ring_one := f.ring_one
  ring_add := f.ring_add
  ring_mul := f.ring_mul

namespace RingedToposMorphism.RingData

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}

local instance (U : Dᵒᵖ) :
    Ring (((sheafCompose K (forget RingCat)).obj B).obj.obj U) :=
  inferInstanceAs (Ring (B.obj.obj U))

local instance (U : Cᵒᵖ) :
    Ring (((sheafCompose J (forget RingCat)).obj A).obj.obj U) :=
  inferInstanceAs (Ring (A.obj.obj U))

/-- The zero generalized element of a ring sheaf. -/
def zero (T : Sheaf K (Type u)) : T ⟶ (sheafCompose K (forget RingCat)).obj B :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ 0)
     naturality := by
       intro U V k
       ext t
       exact (map_zero (B.obj.map k).hom).symm }⟩

/-- The unit generalized element of a ring sheaf. -/
def one (T : Sheaf K (Type u)) : T ⟶ (sheafCompose K (forget RingCat)).obj B :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ 1)
     naturality := by
       intro U V k
       ext t
       exact (map_one (B.obj.map k).hom).symm }⟩

/-- The sum of generalized elements of a ring sheaf. -/
def add {T : Sheaf K (Type u)}
    (x y : T ⟶ (sheafCompose K (forget RingCat)).obj B) :
    T ⟶ (sheafCompose K (forget RingCat)).obj B :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun t ↦ x.hom.app U t + y.hom.app U t)
     naturality := by
       intro U V k
       ext t
       exact (congrArg₂ (· + ·) (ConcreteCategory.congr_hom (x.hom.naturality k) t)
         (ConcreteCategory.congr_hom (y.hom.naturality k) t)).trans
         (map_add (B.obj.map k).hom _ _).symm }⟩

/-- The product of generalized elements of a ring sheaf. -/
def mul {T : Sheaf K (Type u)}
    (x y : T ⟶ (sheafCompose K (forget RingCat)).obj B) :
    T ⟶ (sheafCompose K (forget RingCat)).obj B :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun t ↦ x.hom.app U t * y.hom.app U t)
     naturality := by
       intro U V k
       ext t
       exact (congrArg₂ (· * ·) (ConcreteCategory.congr_hom (x.hom.naturality k) t)
         (ConcreteCategory.congr_hom (y.hom.naturality k) t)).trans
         (map_mul (B.obj.map k).hom _ _).symm }⟩

variable (g : RingedToposMorphism.RingData A B)

/-- A faithful inverse image and monic structural map reflect generalized elements. -/
theorem reflect_eq [g.inverse.Faithful] [Mono g.ringMap]
    {T : Sheaf K (Type u)} (x y : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (h : ∀ (U : Cᵒᵖ) (t : (g.inverse.obj T).obj.obj U),
      ((g.inverse.map x) ≫ g.ringMap).hom.app U t =
        ((g.inverse.map y) ≫ g.ringMap).hom.app U t) : x = y := by
  apply g.inverse.map_injective
  apply (cancel_mono g.ringMap).mp
  ext U t
  exact h U t

/-- Reflection of zero through an invertible structural ring map. -/
theorem reflect_zero [g.inverse.Faithful] [Mono g.ringMap]
    {T : Sheaf K (Type u)} (z : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (h : ∀ (U : Cᵒᵖ) (t : (g.inverse.obj T).obj.obj U),
      ((g.inverse.map z) ≫ g.ringMap).hom.app U t = (0 : A.obj.obj U)) :
    ∀ (U : Dᵒᵖ) (t : T.obj.obj U), z.hom.app U t = (0 : B.obj.obj U) := by
  have hz := g.ring_zero T (zero T) (fun _ _ ↦ rfl)
  have he : z = zero T := g.reflect_eq z (zero T) (fun U t ↦ (h U t).trans (hz U t).symm)
  intro U t
  rw [he]
  rfl

/-- Reflection of one through an invertible structural ring map. -/
theorem reflect_one [g.inverse.Faithful] [Mono g.ringMap]
    {T : Sheaf K (Type u)} (z : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (h : ∀ (U : Cᵒᵖ) (t : (g.inverse.obj T).obj.obj U),
      ((g.inverse.map z) ≫ g.ringMap).hom.app U t = (1 : A.obj.obj U)) :
    ∀ (U : Dᵒᵖ) (t : T.obj.obj U), z.hom.app U t = (1 : B.obj.obj U) := by
  have hz := g.ring_one T (one T) (fun _ _ ↦ rfl)
  have he : z = one T := g.reflect_eq z (one T) (fun U t ↦ (h U t).trans (hz U t).symm)
  intro U t
  rw [he]
  rfl

/-- Reflection of addition through an invertible structural ring map. -/
theorem reflect_add [g.inverse.Faithful] [Mono g.ringMap]
    {T : Sheaf K (Type u)} (x y z : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (h : ∀ (U : Cᵒᵖ) (t : (g.inverse.obj T).obj.obj U),
      ((g.inverse.map z) ≫ g.ringMap).hom.app U t =
        ((g.inverse.map x) ≫ g.ringMap).hom.app U t +
          ((g.inverse.map y) ≫ g.ringMap).hom.app U t) :
    ∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = x.hom.app U t + y.hom.app U t := by
  have hz := g.ring_add T x y (add x y) (fun _ _ ↦ rfl)
  have he : z = add x y :=
    g.reflect_eq z (add x y) (fun U t ↦ (h U t).trans (hz U t).symm)
  intro U t
  rw [he]
  rfl

/-- Reflection of multiplication through an invertible structural ring map. -/
theorem reflect_mul [g.inverse.Faithful] [Mono g.ringMap]
    {T : Sheaf K (Type u)} (x y z : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (h : ∀ (U : Cᵒᵖ) (t : (g.inverse.obj T).obj.obj U),
      ((g.inverse.map z) ≫ g.ringMap).hom.app U t =
        ((g.inverse.map x) ≫ g.ringMap).hom.app U t *
          ((g.inverse.map y) ≫ g.ringMap).hom.app U t) :
    ∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = x.hom.app U t * y.hom.app U t := by
  have hz := g.ring_mul T x y (mul x y) (fun _ _ ↦ rfl)
  have he : z = mul x y :=
    g.reflect_eq z (mul x y) (fun U t ↦ (h U t).trans (hz U t).symm)
  intro U t
  rw [he]
  rfl


/-- A lift of the direct image to modules, with the structural-map-induced action. -/
structure Modules (d : RingedToposMorphism.RingData A B) where
  /-- The induced direct image on module sheaves. -/
  modules : SheafOfModules.{u} A ⥤ SheafOfModules.{u} B
  /-- Additivity of the induced direct image. -/
  additive : modules.Additive
  /-- The underlying direct image of sheaves of sets, naturally in the module. -/
  underlying :
    modules ⋙ SheafOfModules.toSheaf B ⋙ sheafCompose K (forget AddCommGrpCat) ≅
      (SheafOfModules.toSheaf A ⋙ sheafCompose J (forget AddCommGrpCat)) ⋙ d.direct
  /-- Addition and the structural-map-induced scalar action, under adjunction. -/
  module_linear : ∀ (M : SheafOfModules.{u} A) (T : Sheaf K (Type u))
    (a : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (x y z : T ⟶ (sheafCompose K (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf B).obj (modules.obj M))),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((modules.obj M).val.obj U) inferInstance
        (@SMul.smul (B.obj.obj U) ((modules.obj M).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (d.inverse.obj T).obj.obj U),
      ((d.adj.homEquiv T _).symm (z ≫ underlying.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
            (((d.inverse.map a) ≫ d.ringMap).hom.app U t)
            (((d.adj.homEquiv T _).symm (x ≫ underlying.hom.app M)).hom.app U t))
          (((d.adj.homEquiv T _).symm (y ≫ underlying.hom.app M)).hom.app U t)

end RingedToposMorphism.RingData
end CategoryTheory

namespace CategoryTheory.RingedToposMorphism.RingData

section

open CategoryTheory CategoryTheory.Limits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
variable (g : RingedToposMorphism.RingData A B)

/-- Assemble geometric ring data and its induced module direct image. -/
def withModules (d : RingedToposMorphism.RingData A B) (m : d.Modules) :
    RingedToposMorphism A B where
  inverse := d.inverse
  direct := d.direct
  adj := d.adj
  leftExact := d.leftExact
  ringMap := d.ringMap
  ring_zero := d.ring_zero
  ring_one := d.ring_one
  ring_add := d.ring_add
  ring_mul := d.ring_mul
  modules := m.modules
  additive := m.additive
  underlying := m.underlying
  module_linear := m.module_linear

end

end CategoryTheory.RingedToposMorphism.RingData
