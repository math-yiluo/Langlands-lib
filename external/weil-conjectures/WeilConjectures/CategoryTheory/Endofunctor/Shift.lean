/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Shifts on algebras of a shift-commuting endofunctor

Let `C` be a category with a shift by an additive monoid `A`, and let `F : C ⥤ C` be an
endofunctor commuting with the shifts. The shift of an algebra `(K, str)` of `F` by `a : A` is
`K⟦a⟧` with the structure morphism

```
             (F.commShiftIso a).hom.app K          str⟦a⟧'
F (K⟦a⟧) ------------------------------> (F K)⟦a⟧ ---------> K⟦a⟧
```

This defines a shift by `A` on `CategoryTheory.Endofunctor.Algebra F` for which the forgetful
functor commutes with the shifts. As the shift of an algebra whose structure morphism is an
isomorphism has again an invertible structure morphism, the shift restricts to
`CategoryTheory.Endofunctor.IsoAlgebra F`. The shift functor on algebras is itself the transport
`Algebra.mapOfNatTrans` along `shiftFunctor C a`. The transports `Algebra.mapOfNatTrans` and
`IsoAlgebra.mapOfNatIso` along a functor commuting with the shifts commute with the shifts,
provided that the commutation datum with the endofunctors is compatible with the shifts.

## Main definitions and results

- `CategoryTheory.Endofunctor.Algebra.shiftFunctor`: the shift functor on algebras.
- `CategoryTheory.Endofunctor.Algebra.hasShift`: the shift by `A` on `Algebra F`.
- `CategoryTheory.Endofunctor.IsoAlgebra.hasShift`: the shift by `A` on `IsoAlgebra F`.
- `CategoryTheory.Endofunctor.Algebra.commShiftMapOfNatTrans`:
  `Algebra.mapOfNatTrans e` commutes with the shifts.
- `CategoryTheory.Endofunctor.IsoAlgebra.commShiftMapOfNatIso`:
  `IsoAlgebra.mapOfNatIso e` commutes with the shifts.
-/

@[expose] public section

namespace CategoryTheory.Endofunctor

universe v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

namespace Algebra

section Shift

variable (F : C ⥤ C) [F.CommShift A]

/-- The shift by `a : A` of algebras of an endofunctor `F` commuting with the shifts: the
transport `Algebra.mapOfNatTrans` along `shiftFunctor C a` with the commutation isomorphism of
`F`, so that an algebra `(K, str)` is sent to `K⟦a⟧` with the structure morphism

```
             (F.commShiftIso a).hom.app K          str⟦a⟧'
F (K⟦a⟧) ------------------------------> (F K)⟦a⟧ ---------> K⟦a⟧
```
-/
abbrev shiftFunctor (a : A) : Algebra F ⥤ Algebra F :=
  mapOfNatTrans (L := CategoryTheory.shiftFunctor C a) (F.commShiftIso a).hom

@[simp]
lemma shiftFunctor_obj_a (a : A) (K : Algebra F) : ((shiftFunctor A F a).obj K).a = K.a⟦a⟧ :=
  rfl

@[simp]
lemma shiftFunctor_obj_str (a : A) (K : Algebra F) :
    ((shiftFunctor A F a).obj K).str = (F.commShiftIso a).hom.app K.a ≫ K.str⟦a⟧' :=
  rfl

@[simp]
lemma shiftFunctor_map_f (a : A) {K K' : Algebra F} (φ : K ⟶ K') :
    ((shiftFunctor A F a).map φ).f = φ.f⟦a⟧' :=
  rfl

/-- The shift by `0` of algebras is isomorphic to the identity. The component at an algebra
`(K, str)` is `ε = (shiftFunctorZero C A).hom.app K`, which is a morphism of algebras as the
square

```
F (K⟦0⟧) ──F.map ε──▶ F K
   │                    │
 str'                  str
   ▼                    ▼
  K⟦0⟧ ───────ε───────▶ K
```

commutes, where `str' = (F.commShiftIso 0).hom.app K ≫ str⟦0⟧'` is the shifted structure
morphism. -/
noncomputable def shiftFunctorZero : shiftFunctor A F 0 ≅ 𝟭 (Algebra F) :=
  NatIso.ofComponents (fun K ↦ isoMk ((CategoryTheory.shiftFunctorZero C A).app K.a) (by
    simp [F.commShiftIso_zero]))
    (fun φ ↦ Algebra.ext ((CategoryTheory.shiftFunctorZero C A).hom.naturality φ.f))

@[simp]
lemma shiftFunctorZero_hom_app_f (K : Algebra F) :
    ((shiftFunctorZero A F).hom.app K).f = (CategoryTheory.shiftFunctorZero C A).hom.app K.a :=
  rfl

@[simp]
lemma shiftFunctorZero_inv_app_f (K : Algebra F) :
    ((shiftFunctorZero A F).inv.app K).f = (CategoryTheory.shiftFunctorZero C A).inv.app K.a :=
  rfl

/-- The shift by `m + n` of algebras is the composite of the shifts by `m` and by `n`. The
component at an algebra `(K, str)` is `δ = (shiftFunctorAdd C m n).hom.app K`, which is a
morphism of algebras as the square

```
F (K⟦m + n⟧) ─────F.map δ─────▶ F (K⟦m⟧⟦n⟧)
     │                              │
   str'                           str''
     ▼                              ▼
  K⟦m + n⟧ ─────────δ─────────▶  K⟦m⟧⟦n⟧
```

commutes, where `str'` is the structure morphism of the shift by `m + n` and `str''` is the
structure morphism of the shift by `n` of the shift by `m`. -/
noncomputable def shiftFunctorAdd (m n : A) :
    shiftFunctor A F (m + n) ≅ shiftFunctor A F m ⋙ shiftFunctor A F n :=
  NatIso.ofComponents (fun K ↦ isoMk ((CategoryTheory.shiftFunctorAdd C m n).app K.a) (by
    simp [F.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]))
    (fun φ ↦ Algebra.ext ((CategoryTheory.shiftFunctorAdd C m n).hom.naturality φ.f))

@[simp]
lemma shiftFunctorAdd_hom_app_f (m n : A) (K : Algebra F) :
    ((shiftFunctorAdd A F m n).hom.app K).f =
      (CategoryTheory.shiftFunctorAdd C m n).hom.app K.a :=
  rfl

@[simp]
lemma shiftFunctorAdd_inv_app_f (m n : A) (K : Algebra F) :
    ((shiftFunctorAdd A F m n).inv.app K).f =
      (CategoryTheory.shiftFunctorAdd C m n).inv.app K.a :=
  rfl

/-- The data defining the shift by `A` on algebras of an endofunctor commuting with the
shifts. -/
noncomputable def shiftMkCore : ShiftMkCore (Algebra F) A where
  F := shiftFunctor A F
  zero := shiftFunctorZero A F
  add := shiftFunctorAdd A F
  assoc_hom_app m₁ m₂ m₃ K := by
    ext
    simp only [comp_f, eqToHom_f, shiftFunctorAdd_hom_app_f, mapOfNatTrans_map_f]
    exact (shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ K.a).trans
      (by simp [shiftFunctorAdd', eqToHom_app])
  zero_add_hom_app n K := by
    ext
    simp only [comp_f, eqToHom_f, shiftFunctorAdd_hom_app_f, mapOfNatTrans_map_f,
      shiftFunctorZero_inv_app_f]
    exact shiftFunctorAdd_zero_add_hom_app n K.a
  add_zero_hom_app n K := by
    ext
    simp only [comp_f, eqToHom_f, shiftFunctorAdd_hom_app_f, shiftFunctorZero_inv_app_f]
    exact shiftFunctorAdd_add_zero_hom_app n K.a

/-- The shift by `A` on algebras of an endofunctor commuting with the shifts. -/
noncomputable instance hasShift : HasShift (Algebra F) A :=
  hasShiftMk _ _ (shiftMkCore A F)

@[simp]
lemma shiftFunctor_eq (a : A) :
    CategoryTheory.shiftFunctor (Algebra F) a = shiftFunctor A F a :=
  ShiftMkCore.shiftFunctor_eq _ a

@[simp]
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (Algebra F) A = shiftFunctorZero A F :=
  ShiftMkCore.shiftFunctorZero_eq _

@[simp]
lemma shiftFunctorAdd_eq (m n : A) :
    CategoryTheory.shiftFunctorAdd (Algebra F) m n = shiftFunctorAdd A F m n :=
  ShiftMkCore.shiftFunctorAdd_eq _ _ _

variable {A F}

@[simp]
lemma shift_a (K : Algebra F) (a : A) : (K⟦a⟧).a = K.a⟦a⟧ :=
  rfl

@[simp]
lemma shift_str (K : Algebra F) (a : A) :
    (K⟦a⟧).str = (F.commShiftIso a).hom.app K.a ≫ K.str⟦a⟧' :=
  rfl

@[simp]
lemma shift_map_f {K K' : Algebra F} (φ : K ⟶ K') (a : A) : (φ⟦a⟧').f = φ.f⟦a⟧' :=
  rfl

variable (A F)

/-- The forgetful functor from algebras commutes with the shifts, with identity commutation
isomorphisms:

```
Algebra F ──(·)⟦a⟧──▶ Algebra F
    │                     │
  forget               forget
    ▼                     ▼
    C ──────(·)⟦a⟧──────▶ C
```
-/
noncomputable instance commShiftForget : (forget F).CommShift A where
  commShiftIso a := NatIso.ofComponents (fun K ↦ Iso.refl (K.a⟦a⟧))
    (fun φ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)
  commShiftIso_zero := by
    ext K
    rw [Functor.CommShift.isoZero_hom_app]
    exact (Iso.hom_inv_id_app _ _).symm
  commShiftIso_add m n := by
    ext K
    rw [Functor.CommShift.isoAdd_hom_app]
    exact (by simp : 𝟙 (K.a⟦m + n⟧) = (CategoryTheory.shiftFunctorAdd C m n).hom.app K.a ≫
      𝟙 _ ≫ (𝟙 (K.a⟦m⟧))⟦n⟧' ≫ (CategoryTheory.shiftFunctorAdd C m n).inv.app K.a)

@[simp]
lemma forget_commShiftIso_hom_app (a : A) (K : Algebra F) :
    ((forget F).commShiftIso a).hom.app K = 𝟙 (K.a⟦a⟧) :=
  rfl

@[simp]
lemma forget_commShiftIso_inv_app (a : A) (K : Algebra F) :
    ((forget F).commShiftIso a).inv.app K = 𝟙 (K.a⟦a⟧) :=
  rfl

/-- The shift of an algebra with invertible structure morphism has invertible structure
morphism. -/
instance isStableUnderShift_isIsoStr : (IsIsoStr F).IsStableUnderShift A where
  isStableUnderShiftBy a := ⟨fun _ hK ↦ isIsoStr_mapOfNatTrans_obj (F.commShiftIso a).hom hK⟩

end Shift

section Map

variable {F : C ⥤ C} {G : D ⥤ D} [F.CommShift A] [G.CommShift A] {L : C ⥤ D} [L.CommShift A]
  (e : L ⋙ G ⟶ F ⋙ L) [NatTrans.CommShift e A]

/-- The commutation isomorphism `(L.commShiftIso a).hom.app K` is compatible with the structure
morphisms of the transported algebras, when `e` is compatible with the shifts. This follows from
the compatibility square of `e` with the shifts

```
G (L (K⟦a⟧)) ───G.map (L.commShiftIso a).hom───▶ G ((L K)⟦a⟧)
      │                                                │
 e.app (K⟦a⟧)                               (G.commShiftIso a).hom
      ▼                                                ▼
L (F (K⟦a⟧))                                    (G (L K))⟦a⟧
      │                                                │
L.map (F.commShiftIso a).hom                     (e.app K)⟦a⟧'
      ▼                                                ▼
L ((F K)⟦a⟧) ─────(L.commShiftIso a).hom─────▶ (L (F K))⟦a⟧
```

followed by the naturality square of `L.commShiftIso a` at `L.map str`. -/
lemma map_commShiftIso_hom_app_comp_mapOfNatTrans_str (a : A) (K : Algebra F) :
    G.map ((L.commShiftIso a).hom.app K.a) ≫ (G.commShiftIso a).hom.app (L.obj K.a) ≫
        (e.app K.a ≫ L.map K.str)⟦a⟧' =
      (e.app (K.a⟦a⟧) ≫ L.map ((F.commShiftIso a).hom.app K.a ≫ K.str⟦a⟧')) ≫
        (L.commShiftIso a).hom.app K.a := by
  simpa [Functor.commShiftIso_comp_hom_app] using
    NatTrans.shift_app_comm e a K.a =≫ (L.map K.str)⟦a⟧'

/-- The transport of algebras `Algebra.mapOfNatTrans e` commutes with the shifts, with the
commutation isomorphisms of `L` as commutation isomorphisms, when `e` is compatible with the
shifts, see `Algebra.map_commShiftIso_hom_app_comp_mapOfNatTrans_str`. -/
noncomputable instance commShiftMapOfNatTrans : (mapOfNatTrans e).CommShift A where
  commShiftIso a := NatIso.ofComponents
    (fun K ↦ isoMk ((L.commShiftIso a).app K.a)
      (map_commShiftIso_hom_app_comp_mapOfNatTrans_str A e a K))
    (fun φ ↦ Algebra.ext ((L.commShiftIso a).hom.naturality φ.f))
  commShiftIso_zero := by
    ext K
    rw [Functor.CommShift.isoZero_hom_app]
    simp only [L.commShiftIso_zero]
    exact Functor.CommShift.isoZero_hom_app L A K.a
  commShiftIso_add m n := by
    ext K
    rw [Functor.CommShift.isoAdd_hom_app]
    simp only [L.commShiftIso_add]
    exact Functor.CommShift.isoAdd_hom_app _ _ K.a

@[simp]
lemma mapOfNatTrans_commShiftIso_hom_app_f (a : A) (K : Algebra F) :
    (((mapOfNatTrans e).commShiftIso a).hom.app K).f = (L.commShiftIso a).hom.app K.a :=
  rfl

@[simp]
lemma mapOfNatTrans_commShiftIso_inv_app_f (a : A) (K : Algebra F) :
    (((mapOfNatTrans e).commShiftIso a).inv.app K).f = (L.commShiftIso a).inv.app K.a :=
  rfl

end Map

end Algebra

namespace IsoAlgebra

section Shift

variable (F : C ⥤ C) [F.CommShift A]

/-- The shift by `A` on algebras with invertible structure morphism of an endofunctor
commuting with the shifts, restricted from the shift on all algebras. -/
noncomputable instance hasShift : HasShift (IsoAlgebra F) A :=
  inferInstanceAs (HasShift (Algebra.IsIsoStr F).FullSubcategory A)

/-- The inclusion of the algebras with invertible structure morphism into all algebras
commutes with the shifts:

```
IsoAlgebra F ──(·)⟦a⟧──▶ IsoAlgebra F
     │                         │
     ι                         ι
     ▼                         ▼
 Algebra F ────(·)⟦a⟧────▶ Algebra F
```
-/
noncomputable instance commShiftι : (ι F).CommShift A :=
  inferInstanceAs ((Algebra.IsIsoStr F).ι.CommShift A)

/-- The forgetful functor from algebras with invertible structure morphism commutes with the
shifts, with the commutation isomorphisms of `ι F`:

```
IsoAlgebra F ──(·)⟦a⟧──▶ IsoAlgebra F
     │                         │
   forget                    forget
     ▼                         ▼
     C ─────────(·)⟦a⟧───────▶ C
```
-/
noncomputable instance commShiftForget : (forget F).CommShift A :=
  inferInstanceAs ((ι F ⋙ Algebra.forget F).CommShift A)

@[simp]
lemma forget_commShiftIso_hom_app (a : A) (K : IsoAlgebra F) :
    ((forget F).commShiftIso a).hom.app K = (((ι F).commShiftIso a).hom.app K).f :=
  (Functor.commShiftIso_comp_hom_app (ι F) (Algebra.forget F) a K).trans (Category.comp_id _)

@[simp]
lemma forget_commShiftIso_inv_app (a : A) (K : IsoAlgebra F) :
    ((forget F).commShiftIso a).inv.app K = (((ι F).commShiftIso a).inv.app K).f :=
  (Functor.commShiftIso_comp_inv_app (ι F) (Algebra.forget F) a K).trans (Category.id_comp _)

end Shift

section Map

variable {F : C ⥤ C} {G : D ⥤ D} [F.CommShift A] [G.CommShift A] {L : C ⥤ D} [L.CommShift A]

/-- The transport of algebras with invertible structure morphism `IsoAlgebra.mapOfNatIso e`
commutes with the shifts, when `e` is compatible with the shifts, with the commutation
isomorphisms of `L` as commutation isomorphisms:

```
IsoAlgebra F ──mapOfNatIso e──▶ IsoAlgebra G
     │                               │
  (·)⟦a⟧                          (·)⟦a⟧
     ▼                               ▼
IsoAlgebra F ──mapOfNatIso e──▶ IsoAlgebra G
```

It is restricted from `Algebra.commShiftMapOfNatTrans`. -/
noncomputable instance commShiftMapOfNatIso (e : L ⋙ G ≅ F ⋙ L) [NatTrans.CommShift e.hom A] :
    (mapOfNatIso e).CommShift A :=
  inferInstanceAs (((Algebra.IsIsoStr G).lift (ι F ⋙ Algebra.mapOfNatTrans e.hom) _).CommShift A)

end Map

end IsoAlgebra

end CategoryTheory.Endofunctor
