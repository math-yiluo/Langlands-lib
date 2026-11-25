/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Algebras of an endofunctor with invertible structure morphism, and limits of algebras

Let `F : C ⥤ C` be an endofunctor. An algebra of `F` in the sense of
`CategoryTheory.Endofunctor.Algebra` is an object `a` of `C` together with a morphism
`str : F.obj a ⟶ a`. This file studies the algebras whose structure morphism is an
isomorphism: the object property `CategoryTheory.Endofunctor.Algebra.IsIsoStr` and the
full subcategory `CategoryTheory.Endofunctor.IsoAlgebra` it cuts out. Since a morphism of
algebras carries no condition beyond the commuting square, `IsoAlgebra F` is a full
subcategory of `Algebra F` and inherits its category structure, its forgetful functor and
its `ext` and `isoMk` lemmas. The structure isomorphism of such an algebra can be iterated:
`IsoAlgebra.strIterate` is the composite `Φ^[n] : Fⁿ a ≅ a`.

Algebras are also transported along a functor `L : C ⥤ D` equipped with a commutation
datum with the endofunctors: `Algebra.mapOfNatTrans` for a natural transformation
`e : L ⋙ G ⟶ F ⋙ L`, and `IsoAlgebra.mapOfNatIso` for an isomorphism. The case `L = 𝟭 C` is
`CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`, see `Algebra.mapOfNatTransIdIso`.

Finally, the forgetful functor `Algebra.forget F` creates all limits, and it creates the
colimits that `F` preserves, following the proof for Eilenberg–Moore algebras in
`Mathlib.CategoryTheory.Monad.Limits`. The algebras with invertible structure morphism are
closed under the limits and colimits that `F` preserves.

## Main definitions and results

- `CategoryTheory.Endofunctor.Algebra.mapOfNatTrans`: transport of algebras along a
  functor equipped with a commutation transformation with the endofunctors.
- `CategoryTheory.Endofunctor.Algebra.IsIsoStr`: the property of an algebra that its
  structure morphism is an isomorphism.
- `CategoryTheory.Endofunctor.IsoAlgebra`: the category of algebras with invertible
  structure morphism, with its structure isomorphism `IsoAlgebra.str`, its forgetful
  functor `IsoAlgebra.forget`, the iterated structure isomorphism
  `IsoAlgebra.strIterate`, the transport `IsoAlgebra.mapOfNatIso` and its functoriality
  `IsoAlgebra.mapOfNatIsoHom` in the transporting functor.
- `CategoryTheory.Endofunctor.Algebra.forgetCreatesLimits`: `Algebra.forget F` creates limits.
- `CategoryTheory.Endofunctor.Algebra.forgetCreatesColimit`: `Algebra.forget F` creates the
  colimit of a diagram `D` if `F` preserves the colimit of `D ⋙ Algebra.forget F`.
-/

@[expose] public section

namespace CategoryTheory.Endofunctor

open Limits

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Algebra

@[simp]
lemma eqToHom_f {F : C ⥤ C} {A₀ A₁ : Algebra F} (h : A₀ = A₁) :
    (eqToHom h).f = eqToHom (congr_arg (·.a) h) := by
  cases h
  rfl

section Map

variable {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D}

/-- Transport of algebras of `F : C ⥤ C` to algebras of `G : D ⥤ D` along a functor
`L : C ⥤ D` equipped with a commutation transformation `e : L ⋙ G ⟶ F ⋙ L`: an algebra
`(a, str)` of `F` is sent to `L a` with the structure morphism

```
        e.app a          L str
G (L a) -------> L (F a) -------> L a
```

The case `L = 𝟭 C` is `CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`, see
`CategoryTheory.Endofunctor.Algebra.mapOfNatTransIdIso`. -/
@[simps]
def mapOfNatTrans (e : L ⋙ G ⟶ F ⋙ L) : Algebra F ⥤ Algebra G where
  obj A :=
    { a := L.obj A.a
      str := e.app A.a ≫ L.map A.str }
  map {A B} φ :=
    { f := L.map φ.f
      h := by
        have h := e.naturality φ.f
        simp only [Functor.comp_map] at h
        rw [reassoc_of% h, ← L.map_comp, φ.h, L.map_comp, Category.assoc] }
  map_id A := Algebra.ext (L.map_id A.a)
  map_comp φ ψ := Algebra.ext (L.map_comp φ.f ψ.f)

/-- Transport along the identity functor is `CategoryTheory.Endofunctor.Algebra.functorOfNatTrans`.
-/
@[simps!]
def mapOfNatTransIdIso {F G : C ⥤ C} (e : G ⟶ F) :
    mapOfNatTrans (L := 𝟭 C) e ≅ functorOfNatTrans e :=
  NatIso.ofComponents fun A ↦ isoMk (Iso.refl _)

end Map

/-- The property of an algebra of an endofunctor that its structure morphism is an
isomorphism. The full subcategory it cuts out is
`CategoryTheory.Endofunctor.IsoAlgebra`. -/
def IsIsoStr (F : C ⥤ C) : ObjectProperty (Algebra F) :=
  fun A ↦ IsIso A.str

lemma isIsoStr_iff {F : C ⥤ C} (A : Algebra F) : IsIsoStr F A ↔ IsIso A.str :=
  Iff.rfl

/-- Transport along an isomorphism `e` preserves the invertibility of the structure morphism. -/
lemma isIsoStr_mapOfNatTrans_obj {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D}
    (e : L ⋙ G ⟶ F ⋙ L) [IsIso e] {A : Algebra F}
    (hA : IsIsoStr F A) : IsIsoStr G ((mapOfNatTrans e).obj A) := by
  rw [isIsoStr_iff] at hA
  rw [isIsoStr_iff, mapOfNatTrans_obj_str]
  infer_instance

end Algebra

/-- The category of algebras of an endofunctor `F : C ⥤ C` whose structure morphism is an
isomorphism, the full subcategory of `CategoryTheory.Endofunctor.Algebra F` cut out by
`CategoryTheory.Endofunctor.Algebra.IsIsoStr`. An object is an object `a` of `C` together
with an isomorphism `Φ : F.obj a ≅ a`, and a morphism is a morphism of the underlying
objects commuting with the structure isomorphisms. -/
def IsoAlgebra (F : C ⥤ C) : Type max u v :=
  (Algebra.IsIsoStr F).FullSubcategory

namespace IsoAlgebra

variable {F : C ⥤ C}

instance : Category (IsoAlgebra F) :=
  inferInstanceAs (Category (Algebra.IsIsoStr F).FullSubcategory)

instance (K : IsoAlgebra F) : IsIso K.obj.str :=
  K.property

/-- The inclusion of the algebras with invertible structure morphism into all
algebras. -/
def ι (F : C ⥤ C) : IsoAlgebra F ⥤ Algebra F :=
  (Algebra.IsIsoStr F).ι

@[simp]
lemma ι_obj (K : IsoAlgebra F) : (ι F).obj K = K.obj :=
  rfl

@[simp]
lemma ι_map {K K' : IsoAlgebra F} (φ : K ⟶ K') : (ι F).map φ = φ.hom :=
  rfl

/-- The underlying object of an algebra with invertible structure morphism. -/
abbrev carrier (K : IsoAlgebra F) : C :=
  K.obj.a

/-- The structure isomorphism `Φ : F.obj a ≅ a` of an algebra with invertible structure
morphism. -/
noncomputable def str (K : IsoAlgebra F) : F.obj K.carrier ≅ K.carrier :=
  asIso K.obj.str

@[simp]
lemma str_hom (K : IsoAlgebra F) : K.str.hom = K.obj.str :=
  rfl

/-- The algebra with invertible structure morphism given by an object `a` and an
isomorphism `Φ : F.obj a ≅ a`. -/
def mk (a : C) (Φ : F.obj a ≅ a) : IsoAlgebra F :=
  ⟨{ a := a, str := Φ.hom }, inferInstanceAs (IsIso Φ.hom)⟩

@[simp]
lemma mk_obj (a : C) (Φ : F.obj a ≅ a) : (mk a Φ).obj = { a := a, str := Φ.hom } :=
  rfl

@[simp]
lemma mk_carrier (a : C) (Φ : F.obj a ≅ a) : (mk a Φ).carrier = a :=
  rfl

@[simp]
lemma mk_str (a : C) (Φ : F.obj a ≅ a) : (mk a Φ).str = Φ :=
  Iso.ext rfl

/-- The forgetful functor to the underlying category, discarding the structure
isomorphisms. -/
def forget (F : C ⥤ C) : IsoAlgebra F ⥤ C :=
  ι F ⋙ Algebra.forget F

@[simp]
lemma forget_obj (K : IsoAlgebra F) : (forget F).obj K = K.carrier :=
  rfl

@[simp]
lemma forget_map {K K' : IsoAlgebra F} (φ : K ⟶ K') : (forget F).map φ = φ.hom.f :=
  rfl

@[simp]
lemma id_hom_f (K : IsoAlgebra F) : (𝟙 K : K ⟶ K).hom.f = 𝟙 K.carrier :=
  rfl

@[simp, reassoc]
lemma comp_hom_f {K K' K'' : IsoAlgebra F} (φ : K ⟶ K') (ψ : K' ⟶ K'') :
    (φ ≫ ψ).hom.f = φ.hom.f ≫ ψ.hom.f :=
  rfl

/-- The coherently iterated structure isomorphism `Φ^[n] : Fⁿ a ≅ a`, defined recursively
by `Φ^[0] = 𝟙 a` and `Φ^[n + 1] = Φ ∘ F(Φ^[n])`:

```
            F (Φ^[n])         Φ
F (Fⁿ a) -----------> F a -------> a
```
-/
noncomputable def strIterate (K : IsoAlgebra F) :
    ∀ n : ℕ, (F.iterate n).obj K.carrier ≅ K.carrier
  | 0 => Iso.refl K.carrier
  | n + 1 => F.mapIso (K.strIterate n) ≪≫ K.str

@[simp]
lemma strIterate_zero (K : IsoAlgebra F) : K.strIterate 0 = Iso.refl K.carrier :=
  rfl

/-- The recursive description of the iterated structure isomorphism:

```
            F (Φ^[n])         Φ
F (Fⁿ a) -----------> F a -------> a
```
-/
@[simp]
lemma strIterate_succ (K : IsoAlgebra F) (n : ℕ) :
    K.strIterate (n + 1) = F.mapIso (K.strIterate n) ≪≫ K.str :=
  rfl

@[simp]
lemma strIterate_one (K : IsoAlgebra F) : K.strIterate 1 = K.str := by
  ext
  simp

/-- The iterated structure isomorphisms are compatible with addition: up to the identification
`Fᵐ⁺ⁿ a = Fⁿ (Fᵐ a)` of `Functor.iterate_add`, `Φ^[m + n]` is the composite

```
             Fⁿ (Φ^[m])          Φ^[n]
Fⁿ (Fᵐ a) -------------> Fⁿ a --------> a
```
-/
lemma strIterate_add_hom (K : IsoAlgebra F) (m n : ℕ) :
    (K.strIterate (m + n)).hom =
      eqToHom (Functor.congr_obj (F.iterate_add m n) K.carrier) ≫
        (F.iterate n).map (K.strIterate m).hom ≫ (K.strIterate n).hom := by
  induction n with
  | zero => simp
  | succ n ih =>
    change F.map (K.strIterate (m + n)).hom ≫ K.str.hom =
      _ ≫ F.map ((F.iterate n).map (K.strIterate m).hom) ≫ F.map (K.strIterate n).hom ≫ _
    rw [ih, F.map_comp, F.map_comp, eqToHom_map, Category.assoc, Category.assoc]


section Map

variable {G : D ⥤ D} {L : C ⥤ D}

/-- Transport of algebras with invertible structure morphism along a functor `L : C ⥤ D`
equipped with a commutation isomorphism `e : L ⋙ G ≅ F ⋙ L`: the restriction of
`CategoryTheory.Endofunctor.Algebra.mapOfNatTrans`, which is well defined since the
transported structure morphism

```
        e.app a          L Φ
G (L a) -------> L (F a) -----> L a
```

is again an isomorphism. -/
noncomputable def mapOfNatIso (e : L ⋙ G ≅ F ⋙ L) : IsoAlgebra F ⥤ IsoAlgebra G :=
  (Algebra.IsIsoStr G).lift (ι F ⋙ Algebra.mapOfNatTrans e.hom) fun K ↦
    Algebra.isIsoStr_mapOfNatTrans_obj e.hom K.property

@[simp]
lemma mapOfNatIso_obj_carrier (e : L ⋙ G ≅ F ⋙ L) (K : IsoAlgebra F) :
    ((mapOfNatIso e).obj K).carrier = L.obj K.carrier :=
  rfl

@[simp]
lemma mapOfNatIso_obj_str (e : L ⋙ G ≅ F ⋙ L) (K : IsoAlgebra F) :
    ((mapOfNatIso e).obj K).str = e.app K.carrier ≪≫ L.mapIso K.str :=
  Iso.ext rfl

@[simp]
lemma mapOfNatIso_map_hom_f (e : L ⋙ G ≅ F ⋙ L) {K K' : IsoAlgebra F} (φ : K ⟶ K') :
    ((mapOfNatIso e).map φ).hom.f = L.map φ.hom.f :=
  rfl

/-- A natural transformation `α : L ⟶ L'` compatible with commutation isomorphisms
`e : L ⋙ G ≅ F ⋙ L` and `e' : L' ⋙ G ≅ F ⋙ L'`, in the sense that the square

```
           α G
  G ∘ L ────────▶ G ∘ L'
    │               │
  e │               │ e'
    ▼               ▼
  L ∘ F ────────▶ L' ∘ F
           α F
```

commutes, induces a natural transformation `mapOfNatIso e ⟶ mapOfNatIso e'` with components
those of `α`. -/
@[simps]
noncomputable def mapOfNatIsoHom {L' : C ⥤ D} {e : L ⋙ G ≅ F ⋙ L} {e' : L' ⋙ G ≅ F ⋙ L'}
    (α : L ⟶ L') (hα : Functor.whiskerRight α G ≫ e'.hom = e.hom ≫ Functor.whiskerLeft F α) :
    mapOfNatIso e ⟶ mapOfNatIso e' where
  app K := ObjectProperty.homMk
    { f := α.app K.carrier
      h := by
        have h := congr_app hα K.carrier
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
        simp [mapOfNatIso, reassoc_of% h] }
  naturality _ _ φ := ObjectProperty.hom_ext _ (Algebra.Hom.ext (α.naturality φ.hom.f))

end Map

section Map₂

variable {F₁ : C ⥤ C} {F₂ : D ⥤ D}

/-- A pair of algebras with invertible structure morphism, for `F₁` and `F₂`, is an algebra with
invertible structure morphism for the product endofunctor `F₁.prod F₂`, with structure
isomorphism `Φ_K × Φ_L`. -/
noncomputable def prod : IsoAlgebra F₁ × IsoAlgebra F₂ ⥤ IsoAlgebra (F₁.prod F₂) where
  obj KL := mk (KL.1.carrier, KL.2.carrier) (KL.1.str.prod KL.2.str)
  map {KL KL'} φ := ObjectProperty.homMk
    { f := (φ.1.hom.f, φ.2.hom.f)
      h := Prod.ext φ.1.hom.h φ.2.hom.h }

@[simp]
lemma prod_obj_carrier (KL : IsoAlgebra F₁ × IsoAlgebra F₂) :
    (prod.obj KL).carrier = (KL.1.carrier, KL.2.carrier) :=
  rfl

@[simp]
lemma prod_obj_str (KL : IsoAlgebra F₁ × IsoAlgebra F₂) :
    (prod.obj KL).str = KL.1.str.prod KL.2.str :=
  mk_str _ _

variable {E : Type*} [Category* E] {G : E ⥤ E} (B : C ⥤ D ⥤ E)

/-- Transport of algebras with invertible structure morphism along a bifunctor
`B : C ⥤ D ⥤ E` equipped with a commutation isomorphism
`e_{a,b} : G (B a b) ≅ B (F₁ a) (F₂ b)`, natural in `a` and `b` (an isomorphism of functors
`C × D ⥤ E`): the pair `(K, L)` is sent to `B K L` with the structure isomorphism

```
             e                  B Φ_K Φ_L
G (B K L) -------> B (F₁ K) (F₂ L) ---------> B K L
```

It is the one-variable transport `mapOfNatIso e` along `uncurry B`, applied to the product
algebra `prod.obj (K, L)` and curried. This is the transport of Weil structures along a tensor
product. -/
noncomputable def mapOfNatIso₂
    (e : Functor.uncurry.obj B ⋙ G ≅ F₁.prod F₂ ⋙ Functor.uncurry.obj B) :
    IsoAlgebra F₁ ⥤ IsoAlgebra F₂ ⥤ IsoAlgebra G :=
  Functor.curry.obj (prod ⋙ mapOfNatIso e)

@[simp]
lemma mapOfNatIso₂_obj_obj_carrier
    (e : Functor.uncurry.obj B ⋙ G ≅ F₁.prod F₂ ⋙ Functor.uncurry.obj B)
    (K : IsoAlgebra F₁) (L : IsoAlgebra F₂) :
    (((mapOfNatIso₂ B e).obj K).obj L).carrier = (B.obj K.carrier).obj L.carrier :=
  rfl

lemma mapOfNatIso₂_obj_obj_str
    (e : Functor.uncurry.obj B ⋙ G ≅ F₁.prod F₂ ⋙ Functor.uncurry.obj B)
    (K : IsoAlgebra F₁) (L : IsoAlgebra F₂) :
    (((mapOfNatIso₂ B e).obj K).obj L).str =
      e.app (K.carrier, L.carrier) ≪≫ (Functor.uncurry.obj B).mapIso (K.str.prod L.str) := by
  ext
  simp [mapOfNatIso₂]


end Map₂

section Op

/-- An algebra with invertible structure morphism `(a, Φ : F a ≅ a)` of `F` gives an algebra
with invertible structure morphism of `F.op` on `op a`, with structure isomorphism the opposite
of `Φ⁻¹ : a ≅ F a`. This is the contravariant variable of a transport along a bifunctor such as
an internal hom: the structure isomorphism enters through its inverse. -/
noncomputable def opFunctor : (IsoAlgebra F)ᵒᵖ ⥤ IsoAlgebra F.op where
  obj K := mk (Opposite.op K.unop.carrier) K.unop.str.symm.op
  map {K K'} φ := ObjectProperty.homMk
    { f := φ.unop.hom.f.op
      h := by
        apply Quiver.Hom.unop_inj
        have h : F.map φ.unop.hom.f ≫ K.unop.str.hom = K'.unop.str.hom ≫ φ.unop.hom.f :=
          φ.unop.hom.h
        change (K'.unop.str.inv ≫ F.map φ.unop.hom.f) = φ.unop.hom.f ≫ K.unop.str.inv
        rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
          Category.comp_id] }

lemma opFunctor_obj_carrier (K : (IsoAlgebra F)ᵒᵖ) :
    (opFunctor.obj K).carrier = Opposite.op K.unop.carrier :=
  mk_carrier _ _


@[simp]
lemma opFunctor_obj_str (K : (IsoAlgebra F)ᵒᵖ) :
    (opFunctor.obj K).str = K.unop.str.symm.op :=
  mk_str _ _

end Op

end IsoAlgebra

namespace Algebra

variable {F : C ⥤ C} {J : Type w'} [Category.{w} J]

/-- The natural transformation `F (D j) ⟶ D j` given by the structure morphisms of a diagram
`D` of algebras. -/
@[simps]
def strNatTrans (D : J ⥤ Algebra F) : (D ⋙ forget F) ⋙ F ⟶ D ⋙ forget F where
  app j := (D.obj j).str
  naturality _ _ g := (D.map g).h

/-- The natural isomorphism `F (D j) ≅ D j` given by the structure morphisms of a diagram `D`
of algebras with invertible structure morphisms. -/
@[simps! hom]
noncomputable def strNatIso (D : J ⥤ Algebra F) (hD : ∀ j, IsIsoStr F (D.obj j)) :
    (D ⋙ forget F) ⋙ F ≅ D ⋙ forget F :=
  haveI : ∀ j, IsIso ((strNatTrans D).app j) := hD
  haveI : IsIso (strNatTrans D) := NatIso.isIso_of_isIso_app _
  asIso (strNatTrans D)

namespace ForgetCreatesLimits

variable (D : J ⥤ Algebra F) (c : Cone (D ⋙ forget F)) (t : IsLimit c)

/-- (Impl) The cone with point `F c.pt` and components

```
        F (c.π j)           (D j).str
F c.pt ----------> F (D j) ----------> D j
```

Its lift along `c` is the structure morphism of the limit of `D`. -/
@[simps]
def newCone : Cone (D ⋙ forget F) where
  pt := F.obj c.pt
  π :=
    { app j := F.map (c.π.app j) ≫ (D.obj j).str
      naturality X Y g := by
        change 𝟙 (F.obj c.pt) ≫ F.map (c.π.app Y) ≫ (D.obj Y).str =
          (F.map (c.π.app X) ≫ (D.obj X).str) ≫ (D.map g).f
        rw [Category.id_comp, Category.assoc, ← Hom.h, ← F.map_comp_assoc]
        exact congrArg (F.map · ≫ _) (c.w g).symm }

/-- (Impl) The algebra structure on the point of a limit cone of the underlying objects of a
diagram of algebras. -/
@[simps]
def conePoint : Algebra F where
  a := c.pt
  str := t.lift (newCone D c)

/-- (Impl) The lift of a limit cone of the underlying objects of a diagram of algebras to a
cone of algebras. -/
@[simps]
def liftedCone : Cone D where
  pt := conePoint D c t
  π :=
    { app j :=
        { f := c.π.app j
          h := (t.fac (newCone D c) j).symm }
      naturality _ _ g := Hom.ext ((Category.id_comp _).trans (c.w g).symm) }

/-- (Impl) The lifted cone `liftedCone D c t` is a limit cone. -/
def liftedConeIsLimit : IsLimit (liftedCone D c t) where
  lift s :=
    { f := t.lift ((forget F).mapCone s)
      h := t.hom_ext fun j ↦ by
        change (F.map (t.lift ((forget F).mapCone s)) ≫ t.lift (newCone D c)) ≫ c.π.app j =
          (s.pt.str ≫ t.lift ((forget F).mapCone s)) ≫ c.π.app j
        rw [Category.assoc, t.fac, Category.assoc, t.fac, newCone_π_app, ← F.map_comp_assoc,
          t.fac]
        exact (s.π.app j).h }
  fac _ j := Hom.ext (t.fac _ j)
  uniq s m hm := Hom.ext <| t.uniq ((forget F).mapCone s) m.f fun j ↦ congr_arg Hom.f (hm j)

end ForgetCreatesLimits

/-- The forgetful functor from algebras of an endofunctor creates all limits. -/
instance forgetCreatesLimits : CreatesLimitsOfSize.{w, w'} (forget F) where
  CreatesLimitsOfShape :=
    { CreatesLimit {D} := createsLimitOfReflectsIso fun c t ↦
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit D c t } }

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Algebra F) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget F)

instance [HasFiniteLimits C] : HasFiniteLimits (Algebra F) where
  out _ := inferInstance

instance [HasFiniteProducts C] : HasFiniteProducts (Algebra F) where
  out _ := inferInstance

instance [HasFiniteLimits C] : PreservesFiniteLimits (forget F) where
  preservesFiniteLimits _ := inferInstance

namespace ForgetCreatesColimits

variable {D : J ⥤ Algebra F} (c : Cocone (D ⋙ forget F)) (t : IsColimit c)

/-- (Impl) The cocone over `(D ⋙ forget F) ⋙ F` with point `c.pt` and components

```
         (D j).str        c.ι j
F (D j) ----------> D j --------> c.pt
```

Its descent along `F c` is the structure morphism of the colimit of `D`. -/
@[simps]
def newCocone : Cocone ((D ⋙ forget F) ⋙ F) where
  pt := c.pt
  ι := strNatTrans D ≫ c.ι

variable [PreservesColimit (D ⋙ forget F) F]

/-- (Impl) The algebra structure on the point of a colimit cocone of the underlying objects of
a diagram of algebras, when `F` preserves the colimit. -/
@[simps]
noncomputable def coconePoint : Algebra F where
  a := c.pt
  str := (isColimitOfPreserves F t).desc (newCocone c)

/-- (Impl) The lift of a colimit cocone of the underlying objects of a diagram of algebras to
a cocone of algebras. -/
@[simps]
noncomputable def liftedCocone : Cocone D where
  pt := coconePoint c t
  ι :=
    { app j :=
        { f := c.ι.app j
          h := (isColimitOfPreserves F t).fac (newCocone c) j }
      naturality _ _ g := Hom.ext ((c.w g).trans (Category.comp_id _).symm) }

/-- (Impl) The lifted cocone `liftedCocone c t` is a colimit cocone. -/
noncomputable def liftedCoconeIsColimit : IsColimit (liftedCocone c t) where
  desc s :=
    { f := t.desc ((forget F).mapCocone s)
      h := (isColimitOfPreserves F t).hom_ext fun j ↦ by
        have hd : c.ι.app j ≫ t.desc ((forget F).mapCocone s) = (s.ι.app j).f := t.fac _ j
        have hs : F.map (c.ι.app j) ≫ (isColimitOfPreserves F t).desc (newCocone c) =
            (D.obj j).str ≫ c.ι.app j :=
          (isColimitOfPreserves F t).fac (newCocone c) j
        change F.map (c.ι.app j) ≫ F.map (t.desc ((forget F).mapCocone s)) ≫ s.pt.str =
          F.map (c.ι.app j) ≫ (isColimitOfPreserves F t).desc (newCocone c) ≫
            t.desc ((forget F).mapCocone s)
        rw [← F.map_comp_assoc, hd, ← Category.assoc, hs, Category.assoc, hd]
        exact (s.ι.app j).h }
  fac _ j := Hom.ext (t.fac _ j)
  uniq s m hm := Hom.ext <| t.uniq ((forget F).mapCocone s) m.f fun j ↦ congr_arg Hom.f (hm j)

end ForgetCreatesColimits

/-- The forgetful functor from algebras of an endofunctor creates the colimit of a diagram `D`
if the endofunctor preserves the colimit of the underlying diagram. -/
noncomputable instance forgetCreatesColimit (D : J ⥤ Algebra F)
    [PreservesColimit (D ⋙ forget F) F] : CreatesColimit D (forget F) :=
  createsColimitOfReflectsIso fun c t ↦
    { liftedCocone := ForgetCreatesColimits.liftedCocone c t
      validLift := Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _
      makesColimit := ForgetCreatesColimits.liftedCoconeIsColimit c t }

/-- The forgetful functor from algebras of an endofunctor creates the colimits of the shapes
whose colimits the endofunctor preserves. -/
noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J F] :
    CreatesColimitsOfShape J (forget F) where

instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    HasColimitsOfShape J (Algebra F) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget F)

instance [HasFiniteColimits C] [PreservesFiniteColimits F] :
    PreservesFiniteColimits (forget F) where
  preservesFiniteColimits _ := inferInstance

/-- The structure morphism of the point of a limit of algebras with invertible structure
morphisms is invertible, if `F` preserves the limit: it agrees with the comparison isomorphism
`F (lim D) ≅ lim D` between the limits of `F (D j)` and of `D j` induced by the structure
isomorphisms, since the square

```
         c.pt.str
F c.pt -----------> c.pt
   |                  |
F (π j)              π j
   v                  v
F (D j) ----------> D j
         (D j).str
```

commutes. -/
lemma isIsoStr_of_isLimit {D : J ⥤ Algebra F} {c : Cone D} (hc : IsLimit c)
    [PreservesLimit (D ⋙ forget F) F] [PreservesLimit D (forget F)]
    (hD : ∀ j, IsIsoStr F (D.obj j)) : IsIsoStr F c.pt := by
  let t : IsLimit ((forget F).mapCone c) := isLimitOfPreserves (forget F) hc
  have h : c.pt.str =
      (IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves F t) t (strNatIso D hD)).hom :=
    t.hom_ext fun j ↦ (c.π.app j).h.symm.trans
      (IsLimit.conePointsIsoOfNatIso_hom_comp (isLimitOfPreserves F t) t (strNatIso D hD) j).symm
  rw [isIsoStr_iff, h]
  infer_instance

/-- The structure morphism of the point of a colimit of algebras with invertible structure
morphisms is invertible, if `F` preserves the colimit: it agrees with the comparison
isomorphism `F (colim D) ≅ colim D` between the colimits of `F (D j)` and of `D j` induced by
the structure isomorphisms, since the square

```
         (D j).str
F (D j) ----------> D j
   |                  |
F (ι j)              ι j
   v                  v
F c.pt -----------> c.pt
         c.pt.str
```

commutes. -/
lemma isIsoStr_of_isColimit {D : J ⥤ Algebra F} {c : Cocone D} (hc : IsColimit c)
    [PreservesColimit (D ⋙ forget F) F] [PreservesColimit D (forget F)]
    (hD : ∀ j, IsIsoStr F (D.obj j)) : IsIsoStr F c.pt := by
  let t : IsColimit ((forget F).mapCocone c) := isColimitOfPreserves (forget F) hc
  have h : c.pt.str =
      (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves F t) t (strNatIso D hD)).hom :=
    (isColimitOfPreserves F t).hom_ext fun j ↦ (c.ι.app j).h.trans
      (IsColimit.comp_coconePointsIsoOfNatIso_hom (isColimitOfPreserves F t) t
        (strNatIso D hD) j).symm
  rw [isIsoStr_iff, h]
  infer_instance

instance [HasLimitsOfShape J C] [PreservesLimitsOfShape J F] :
    (IsIsoStr F).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro _ ⟨h⟩
    exact isIsoStr_of_isLimit h.isLimit h.prop_diag_obj

instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    (IsIsoStr F).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro _ ⟨h⟩
    exact isIsoStr_of_isColimit h.isColimit h.prop_diag_obj

instance [HasFiniteProducts C] [PreservesFiniteProducts F] :
    (IsIsoStr F).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    have := Fintype.ofFinite J
    infer_instance

end Algebra

end CategoryTheory.Endofunctor
