/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport

/-!
# Transported connecting morphisms

Let `ι : C ⥤ D` and `ι' : C' ⥤ D'` be functors to categories with a shift by `ℤ` (typically
fully faithful inclusions of full subcategories of triangulated categories which are not
themselves known to be stable under the shift), and `F : C ⥤ C'` a functor which *lifts* a
functor `R : D ⥤ D'` commuting with the shifts, through an isomorphism `F ⋙ ι' ≅ ι ⋙ R`
(`CategoryTheory.Functor.ShiftLift`). A morphism `δ : ι c ⟶ (ι a)[1]` is then sent to a morphism
`ι' (F c) ⟶ (ι' (F a))[1]` (`CategoryTheory.Functor.ShiftLift.connecting`), for instance the
image of the connecting morphism of a distinguished triangle.

A natural transformation `τ : F ⟶ G` between two such functors *commutes with the connecting
morphisms* (`CategoryTheory.NatTrans.CommConnecting`) if
`ι' (τ_c) ≫ G δ = F δ ≫ ι' (τ_a)[1]` for all `δ`. This holds for the restriction of a natural
transformation between the ambient functors which commutes with the shifts
(`CategoryTheory.NatTrans.CommConnecting.of_ambient`), and is stable under composition,
inverses, whiskering, the associators and unitors, mates and conjugates, so that it can be
verified for transformations assembled from units and counits of restricted adjunctions.

## Main definitions

- `CategoryTheory.Functor.ShiftLift`: a lift of a functor commuting with the shifts.
- `CategoryTheory.Functor.ShiftLift.connecting`: the transported connecting morphism.
- `CategoryTheory.NatTrans.CommConnecting`: natural transformations commuting with the
  transported connecting morphisms.
-/

@[expose] public section

namespace CategoryTheory

open Category

variable {Cx Cs Ct Cu Dx Ds Dt Du : Type*} [Category Cx] [Category Cs] [Category Ct]
  [Category Cu] [Category Dx] [Category Ds] [Category Dt] [Category Du]
  [HasShift Dx ℤ] [HasShift Ds ℤ] [HasShift Dt ℤ] [HasShift Du ℤ]

/-- A *lift* of `F : Cx ⥤ Cs` along `ι : Cx ⥤ Dx` and `ιs : Cs ⥤ Ds` to a functor
`Dx ⥤ Ds` commuting with the shifts by `ℤ`: a functor `lift` with a `CommShift` structure and an
isomorphism `F ⋙ ιs ≅ ι ⋙ lift`. -/
class Functor.ShiftLift {Cx Cs Dx : Type*} {Ds : outParam Type*} [Category Cx] [Category Cs]
    [Category Dx] [outParam (Category Ds)] [HasShift Dx ℤ] [outParam (HasShift Ds ℤ)]
    (ι : Cx ⥤ Dx) (F : Cx ⥤ Cs) (ιs : outParam (Cs ⥤ Ds)) where
  /-- The lifted functor. -/
  lift : Dx ⥤ Ds
  /-- The lifted functor commutes with the shifts. -/
  [commShift : lift.CommShift ℤ]
  /-- The comparison isomorphism. -/
  iso : F ⋙ ιs ≅ ι ⋙ lift

attribute [instance_reducible, instance] Functor.ShiftLift.commShift

/-- The comparison isomorphism `F ⋙ ιs ≅ ι ⋙ lift` of a lifted functor, with explicit
arguments. -/
abbrev Functor.ShiftLift.e {Cx Cs Dx Ds : Type*} [Category Cx] [Category Cs] [Category Dx]
    [Category Ds] [HasShift Dx ℤ] [HasShift Ds ℤ] (ι : Cx ⥤ Dx) {ιs : Cs ⥤ Ds} (F : Cx ⥤ Cs)
    [Functor.ShiftLift ι F ιs] : F ⋙ ιs ≅ ι ⋙ Functor.ShiftLift.lift ι F :=
  Functor.ShiftLift.iso

namespace Functor.ShiftLift

variable (ι : Cx ⥤ Dx) (ιs : Cs ⥤ Ds) (ιt : Ct ⥤ Dt) (ιu : Cu ⥤ Du)

/-- The connecting morphism `ιs (F c) ⟶ (ιs (F a))[1]` corresponding to
`δ : ι c ⟶ (ι a)[1]`, through the lift of `F`. -/
noncomputable def connecting (F : Cx ⥤ Cs) [ShiftLift ι F ιs] {a c : Cx}
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    ιs.obj (F.obj c) ⟶ (shiftFunctor Ds (1 : ℤ)).obj (ιs.obj (F.obj a)) :=
  (e ι F).hom.app c ≫ (lift ι F).map δ ≫
    ((lift ι F).commShiftIso (1 : ℤ)).hom.app (ι.obj a) ≫
    (shiftFunctor Ds (1 : ℤ)).map ((e ι F).inv.app a)

variable {ι ιs} in
/-- The transported connecting morphism is natural in its source. -/
lemma connecting_map_comp (F : Cx ⥤ Cs) [ShiftLift ι F ιs] {a c c' : Cx} (g : c' ⟶ c)
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connecting ι ιs F (ι.map g ≫ δ) = ιs.map (F.map g) ≫ connecting ι ιs F δ := by
  have h := (e ι F).hom.naturality g
  simp only [Functor.comp_map] at h
  simp only [connecting, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h]

variable {ι ιs} in
/-- The transported connecting morphism is natural in its target. -/
lemma connecting_comp_shift_map (F : Cx ⥤ Cs) [ShiftLift ι F ιs] {a a' c : Cx} (g : a ⟶ a')
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connecting ι ιs F (δ ≫ (shiftFunctor Dx (1 : ℤ)).map (ι.map g)) =
      connecting ι ιs F δ ≫ (shiftFunctor Ds (1 : ℤ)).map (ιs.map (F.map g)) := by
  have h := (e ι F).inv.naturality g
  simp only [Functor.comp_map] at h
  have h' := ((lift ι F).commShiftIso (1 : ℤ)).hom.naturality (ι.map g)
  simp only [Functor.comp_map] at h'
  simp only [connecting, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h', ← Functor.map_comp, h, Functor.map_comp]

/-- The identity functor lifts the identity functor. -/
noncomputable instance id : ShiftLift ι (𝟭 Cx) ι where
  lift := 𝟭 Dx
  iso := Functor.leftUnitor ι ≪≫ (Functor.rightUnitor ι).symm

/-- A composite of lifted functors lifts the composite. -/
noncomputable instance comp (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) [ShiftLift ι F ιs]
    [ShiftLift ιs G ιt] : ShiftLift ι (F ⋙ G) ιt where
  lift := lift ι F ⋙ lift ιs G
  iso := Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (e ιs G) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (e ι F) _ ≪≫
    Functor.associator _ _ _

/-- The lift of the identity functor is the identity functor. -/
lemma id_lift : lift ι (𝟭 Cx) = 𝟭 Dx := rfl


/-- The lift of a composite is the composite of the lifts. -/
lemma comp_lift (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) [ShiftLift ι F ιs] [ShiftLift ιs G ιt] :
    lift ι (F ⋙ G) = lift ι F ⋙ lift ιs G := rfl

/-- The comparison isomorphism of the identity functor has identity components. -/
@[simp]
lemma id_e_hom_app (c : Cx) : (e ι (𝟭 Cx)).hom.app c = 𝟙 _ := by
  simp [ShiftLift.e, ShiftLift.iso]

/-- The inverse comparison isomorphism of the identity functor has identity components. -/
@[simp]
lemma id_e_inv_app (c : Cx) : (e ι (𝟭 Cx)).inv.app c = 𝟙 _ := by
  simp [ShiftLift.e, ShiftLift.iso]
  rfl

/-- The components of the comparison isomorphism of a composite. -/
@[simp]
lemma comp_e_hom_app (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) [ShiftLift ι F ιs] [ShiftLift ιs G ιt]
    (c : Cx) : (e ι (F ⋙ G)).hom.app c =
      (e ιs G).hom.app (F.obj c) ≫ (lift ιs G).map ((e ι F).hom.app c) := by
  simp [ShiftLift.e, ShiftLift.iso]

/-- The components of the inverse comparison isomorphism of a composite. -/
@[simp]
lemma comp_e_inv_app (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) [ShiftLift ι F ιs] [ShiftLift ιs G ιt]
    (c : Cx) : (e ι (F ⋙ G)).inv.app c =
      (lift ιs G).map ((e ι F).inv.app c) ≫ (e ιs G).inv.app (F.obj c) := by
  simp only [ShiftLift.e, ShiftLift.iso, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

variable {ι} in
/-- The connecting morphism through the identity functor is the original one. -/
@[simp]
lemma connecting_id {a c : Cx} (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connecting ι ι (𝟭 Cx) δ = δ := by
  simp only [connecting, id_e_hom_app, id_e_inv_app]
  erw [Functor.map_id, Category.comp_id, Functor.commShiftIso_id_hom_app, Category.comp_id]
  exact Category.id_comp δ

variable {ι ιs ιt} in
/-- The connecting morphism through a composite is the iterated connecting morphism. -/
lemma connecting_comp (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) [ShiftLift ι F ιs] [ShiftLift ιs G ιt]
    {a c : Cx} (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connecting ι ιt (F ⋙ G) δ = connecting ιs ιt G (connecting ι ιs F δ) := by
  simp only [connecting, comp_e_hom_app, comp_e_inv_app, Functor.map_comp,
    Category.assoc]
  erw [Functor.commShiftIso_comp_hom_app]
  simp only [Category.assoc]
  have h := ((lift ιs G).commShiftIso (1 : ℤ)).hom.naturality ((e ι F).inv.app a)
  simp only [Functor.comp_map] at h
  erw [reassoc_of% h]
  rfl

variable {ι ιs} in
/-- The connecting morphism through `𝟭 ⋙ F` is the one through `F`. -/
lemma connecting_id_comp (F : Cx ⥤ Cs) [ShiftLift ι F ιs] {a c : Cx}
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connecting ι ιs (𝟭 Cx ⋙ F) δ = connecting ι ιs F δ := by
  rw [connecting_comp, connecting_id]

variable {ι ιs} in
/-- The connecting morphism through `F ⋙ 𝟭` is the one through `F`. -/
lemma connecting_comp_id (F : Cx ⥤ Cs) [ShiftLift ι F ιs] {a c : Cx}
    (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    connecting ι ιs (F ⋙ 𝟭 Cs) δ = connecting ι ιs F δ := by
  rw [connecting_comp, connecting_id]


end Functor.ShiftLift

open Functor.ShiftLift

/-- A natural transformation `τ : F ⟶ G` between lifted functors *commutes with the connecting
morphisms* if `ιs (τ_c) ≫ G δ = F δ ≫ ιs (τ_a)[1]` for all `δ : ι c ⟶ (ι a)[1]`, where `F δ` and
`G δ` are the transported connecting morphisms `Functor.ShiftLift.connecting`. -/
class NatTrans.CommConnecting (ι : Cx ⥤ Dx) {ιs : outParam (Cs ⥤ Ds)} {F G : Cx ⥤ Cs}
    [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs] (τ : F ⟶ G) : Prop where
  comm {a c : Cx} (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)) :
    ιs.map (τ.app c) ≫ connecting ι ιs G δ =
      connecting ι ιs F δ ≫ (shiftFunctor Ds (1 : ℤ)).map (ιs.map (τ.app a))

namespace NatTrans.CommConnecting

variable {ι : Cx ⥤ Dx} {ιs : Cs ⥤ Ds} {ιt : Ct ⥤ Dt} {ιu : Cu ⥤ Du}

/-- The restriction of a natural transformation of the lifts which commutes with the shifts
commutes with the connecting morphisms. -/
lemma of_ambient {F G : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    (τ : F ⟶ G) (τ' : lift ι F ⟶ lift ι G) [NatTrans.CommShift τ' ℤ]
    (h : ∀ c : Cx, ιs.map (τ.app c) ≫ (e ι G).hom.app c =
      (e ι F).hom.app c ≫ τ'.app (ι.obj c)) :
    NatTrans.CommConnecting ι τ where
  comm {a c} δ := by
    have h₁ := τ'.naturality δ
    have h₂ := NatTrans.shift_app_comm τ' (1 : ℤ) (ι.obj a)
    have h₃ : (e ι F).inv.app a ≫ ιs.map (τ.app a) =
        τ'.app (ι.obj a) ≫ (e ι G).inv.app a := by
      rw [← cancel_epi ((e ι F).hom.app a), Iso.hom_inv_id_app_assoc, ← reassoc_of% (h a),
        Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    simp only [connecting, Category.assoc]
    rw [reassoc_of% (h c), ← Functor.map_comp, h₃, Functor.map_comp, reassoc_of% h₂,
      reassoc_of% h₁]

/-- The identity transformation commutes with the connecting morphisms. -/
instance id (F : Cx ⥤ Cs) [Functor.ShiftLift ι F ιs] : NatTrans.CommConnecting ι (𝟙 F) where
  comm δ := by simp

/-- A composite of transformations commuting with the connecting morphisms commutes with them. -/
instance comp {F G H : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    [Functor.ShiftLift ι H ιs] (τ : F ⟶ G) (τ' : G ⟶ H) [NatTrans.CommConnecting ι τ]
    [NatTrans.CommConnecting ι τ'] : NatTrans.CommConnecting ι (τ ≫ τ') where
  comm δ := by
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [CommConnecting.comm (τ := τ') δ, reassoc_of% (CommConnecting.comm (τ := τ) δ)]

/-- A composite of natural transformations commuting with the connecting morphisms commutes with
them (with explicit hypotheses). -/
lemma of_comp {F G H : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    [Functor.ShiftLift ι H ιs] {τ : F ⟶ G} {τ' : G ⟶ H} (h : NatTrans.CommConnecting ι τ)
    (h' : NatTrans.CommConnecting ι τ') : NatTrans.CommConnecting ι (τ ≫ τ') :=
  comp τ τ'

/-- The inverse of an isomorphism commuting with the connecting morphisms commutes with them. -/
lemma of_iso_inv {F G : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    (e : F ≅ G) [he : NatTrans.CommConnecting ι e.hom] : NatTrans.CommConnecting ι e.inv where
  comm {a c} δ := by
    have h := he.comm (a := a) (c := c) δ
    rw [← cancel_mono ((shiftFunctor Ds (1 : ℤ)).map (ιs.map (e.hom.app a))), Category.assoc,
      ← h]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc]

/-- The inverse of an isomorphism commuting with the connecting morphisms commutes with them. -/
instance inv {F G : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    (τ : F ⟶ G) [IsIso τ] [NatTrans.CommConnecting ι τ] :
    NatTrans.CommConnecting ι (inv τ) :=
  haveI : NatTrans.CommConnecting ι (asIso τ).hom := ‹NatTrans.CommConnecting ι τ›
  of_iso_inv (asIso τ)

/-- A composite of isomorphisms commuting with the connecting morphisms commutes with them. -/
instance trans_hom {F G H : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    [Functor.ShiftLift ι H ιs] (e : F ≅ G) (e' : G ≅ H) [NatTrans.CommConnecting ι e.hom]
    [NatTrans.CommConnecting ι e'.hom] : NatTrans.CommConnecting ι (e ≪≫ e').hom :=
  comp e.hom e'.hom

/-- The inverse of an isomorphism commuting with the connecting morphisms commutes with them. -/
instance symm_hom {F G : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι G ιs]
    (e : F ≅ G) [NatTrans.CommConnecting ι e.hom] : NatTrans.CommConnecting ι e.symm.hom :=
  of_iso_inv e

/-- Whiskering on the left preserves commuting with the connecting morphisms. -/
instance whiskerLeft (F : Cx ⥤ Cs) [Functor.ShiftLift ι F ιs] {G G' : Cs ⥤ Ct}
    [Functor.ShiftLift ιs G ιt] [Functor.ShiftLift ιs G' ιt] (τ : G ⟶ G')
    [NatTrans.CommConnecting ιs τ] : NatTrans.CommConnecting ι (Functor.whiskerLeft F τ) where
  comm δ := by
    simp only [Functor.whiskerLeft_app, connecting_comp]
    exact CommConnecting.comm _

/-- Whiskering on the right preserves commuting with the connecting morphisms. -/
instance whiskerRight {F F' : Cx ⥤ Cs} [Functor.ShiftLift ι F ιs] [Functor.ShiftLift ι F' ιs]
    (τ : F ⟶ F') [NatTrans.CommConnecting ι τ] (H : Cs ⥤ Ct) [Functor.ShiftLift ιs H ιt] :
    NatTrans.CommConnecting ι (Functor.whiskerRight τ H) where
  comm δ := by
    simp only [Functor.whiskerRight_app, connecting_comp]
    rw [← connecting_map_comp, CommConnecting.comm, connecting_comp_shift_map]

/-- The associator commutes with the connecting morphisms. -/
instance associator_hom (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) (H : Ct ⥤ Cu) [Functor.ShiftLift ι F ιs]
    [Functor.ShiftLift ιs G ιt] [Functor.ShiftLift ιt H ιu] :
    NatTrans.CommConnecting ι (Functor.associator F G H).hom where
  comm δ := by simp [connecting_comp]

/-- The inverse associator commutes with the connecting morphisms. -/
instance associator_inv (F : Cx ⥤ Cs) (G : Cs ⥤ Ct) (H : Ct ⥤ Cu) [Functor.ShiftLift ι F ιs]
    [Functor.ShiftLift ιs G ιt] [Functor.ShiftLift ιt H ιu] :
    NatTrans.CommConnecting ι (Functor.associator F G H).inv where
  comm δ := by simp [connecting_comp]

/-- The left unitor commutes with the connecting morphisms. -/
instance leftUnitor_hom (F : Cx ⥤ Cs) [Functor.ShiftLift ι F ιs] :
    NatTrans.CommConnecting ι (Functor.leftUnitor F).hom where
  comm δ := by simp [connecting_comp]

/-- The inverse left unitor commutes with the connecting morphisms. -/
instance leftUnitor_inv (F : Cx ⥤ Cs) [Functor.ShiftLift ι F ιs] :
    NatTrans.CommConnecting ι (Functor.leftUnitor F).inv where
  comm δ := by simp [connecting_comp]

/-- The right unitor commutes with the connecting morphisms. -/
instance rightUnitor_hom (F : Cx ⥤ Cs) [Functor.ShiftLift ι F ιs] :
    NatTrans.CommConnecting ι (Functor.rightUnitor F).hom where
  comm δ := by simp [connecting_comp]

/-- The inverse right unitor commutes with the connecting morphisms. -/
instance rightUnitor_inv (F : Cx ⥤ Cs) [Functor.ShiftLift ι F ιs] :
    NatTrans.CommConnecting ι (Functor.rightUnitor F).inv where
  comm δ := by simp [connecting_comp]

/-- Commuting with the connecting morphisms only depends on the transported connecting
morphisms, not on the chosen lifts. -/
lemma of_connecting_eq {F G : Cx ⥤ Cs} (I₁ I₂ : Functor.ShiftLift ι F ιs)
    (J₁ J₂ : Functor.ShiftLift ι G ιs) (τ : F ⟶ G)
    (h : letI := I₁; letI := J₁; NatTrans.CommConnecting ι τ)
    (hF : ∀ {a c : Cx} (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)),
      (letI := I₁; connecting ι ιs F δ) = (letI := I₂; connecting ι ιs F δ))
    (hG : ∀ {a c : Cx} (δ : ι.obj c ⟶ (shiftFunctor Dx (1 : ℤ)).obj (ι.obj a)),
      (letI := J₁; connecting ι ιs G δ) = (letI := J₂; connecting ι ιs G δ)) :
    letI := I₂; letI := J₂; NatTrans.CommConnecting ι τ where
  comm δ := by
    rw [← hF, ← hG]
    exact h.comm δ

/-- The `eqToHom` of an equality `P a = P b` induced by an equality `a = b`, for a family of
lifted functors `P`, commutes with the connecting morphisms. -/
lemma eqToHom_congrArg {α : Sort*} (P : α → Cx ⥤ Cs) [∀ x, Functor.ShiftLift ι (P x) ιs]
    {x y : α} (h : x = y) : NatTrans.CommConnecting ι (eqToHom (congrArg P h)) := by
  subst h
  exact id _

end NatTrans.CommConnecting

/-! ### Adjunctions -/

namespace NatTrans.CommConnecting

variable {ι : Cx ⥤ Dx} {ιs : Cs ⥤ Ds} {ιt : Ct ⥤ Dt} {ιu : Cu ⥤ Du}

/-- The unit of an adjunction restricted along fully faithful functors from an adjunction of
the lifts commuting with the shifts commutes with the connecting morphisms. -/
instance restrictFullyFaithful_unit {L : Cx ⥤ Cs} {R : Cs ⥤ Cx} [Functor.ShiftLift ι L ιs]
    [Functor.ShiftLift ιs R ι] (adj : lift ι L ⊣ lift ιs R) [adj.CommShift ℤ]
    (hι : ι.FullyFaithful) (hιs : ιs.FullyFaithful) :
    NatTrans.CommConnecting ι (adj.restrictFullyFaithful hι hιs (e ι L).symm
      (e ιs R).symm).unit :=
  of_ambient _ adj.unit fun c ↦ by
    simp only [Functor.id_obj, Functor.comp_obj, Adjunction.map_restrictFullyFaithful_unit_app,
      Iso.symm_hom, comp_e_hom_app, assoc, Iso.inv_hom_id_app_assoc, id_e_hom_app, id_comp]
    erw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]

/-- The counit of an adjunction restricted along fully faithful functors from an adjunction of
the lifts commuting with the shifts commutes with the connecting morphisms. -/
instance restrictFullyFaithful_counit {L : Cx ⥤ Cs} {R : Cs ⥤ Cx} [Functor.ShiftLift ι L ιs]
    [Functor.ShiftLift ιs R ι] (adj : lift ι L ⊣ lift ιs R) [adj.CommShift ℤ]
    (hι : ι.FullyFaithful) (hιs : ιs.FullyFaithful) :
    NatTrans.CommConnecting ιs (adj.restrictFullyFaithful hι hιs (e ι L).symm
      (e ιs R).symm).counit :=
  of_ambient _ adj.counit fun c ↦ by
    simp

section Mates

variable {G : Cx ⥤ Cs} {L₁ : Cx ⥤ Ct} {L₂ : Cs ⥤ Cu} {H : Ct ⥤ Cu} {R₁ : Ct ⥤ Cx} {R₂ : Cu ⥤ Cs}
  [Functor.ShiftLift ι G ιs] [Functor.ShiftLift ι L₁ ιt] [Functor.ShiftLift ιs L₂ ιu]
  [Functor.ShiftLift ιt H ιu] [Functor.ShiftLift ιt R₁ ι] [Functor.ShiftLift ιu R₂ ιs]

/-- The mate of a natural transformation commuting with the connecting morphisms, for
adjunctions whose units and counits commute with the connecting morphisms, commutes with
them. -/
lemma mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [NatTrans.CommConnecting ι adj₁.unit]
    [NatTrans.CommConnecting ιt adj₁.counit] [NatTrans.CommConnecting ιs adj₂.unit]
    [NatTrans.CommConnecting ιu adj₂.counit] (α : TwoSquare G L₁ L₂ H)
    [NatTrans.CommConnecting ι α] :
    NatTrans.CommConnecting ιt (CategoryTheory.mateEquiv adj₁ adj₂ α) := by
  dsimp only [CategoryTheory.mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk]
  infer_instance

end Mates

/-- The conjugate of a natural transformation commuting with the connecting morphisms, for
adjunctions whose units and counits commute with the connecting morphisms, commutes with
them. -/
lemma conjugateEquiv {L₁ L₂ : Cx ⥤ Cs} {R₁ R₂ : Cs ⥤ Cx} [Functor.ShiftLift ι L₁ ιs]
    [Functor.ShiftLift ι L₂ ιs] [Functor.ShiftLift ιs R₁ ι] [Functor.ShiftLift ιs R₂ ι]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [NatTrans.CommConnecting ι adj₁.unit]
    [NatTrans.CommConnecting ιs adj₁.counit] [NatTrans.CommConnecting ι adj₂.unit]
    [NatTrans.CommConnecting ιs adj₂.counit] (α : L₂ ⟶ L₁) [NatTrans.CommConnecting ι α] :
    NatTrans.CommConnecting ιs (CategoryTheory.conjugateEquiv adj₁ adj₂ α) := by
  have : NatTrans.CommConnecting ι
      (TwoSquare.mk _ _ _ _ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv)) := by
    dsimp only [TwoSquare.mk]
    infer_instance
  have := mateEquiv (ι := ι) (ιs := ι) (ιt := ιs) (ιu := ιs) (G := 𝟭 Cx) (H := 𝟭 Cs) adj₁ adj₂
    (TwoSquare.mk _ _ _ _ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv))
  have e : CategoryTheory.conjugateEquiv adj₁ adj₂ α = R₁.rightUnitor.inv ≫
      (CategoryTheory.mateEquiv adj₁ adj₂
        (TwoSquare.mk _ _ _ _ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv))) ≫
      R₂.leftUnitor.hom := rfl
  rw [e]
  infer_instance

section Comp

variable {F : Cx ⥤ Cs} {G : Cs ⥤ Cx} {H : Cs ⥤ Ct} {I : Ct ⥤ Cs} [Functor.ShiftLift ι F ιs]
  [Functor.ShiftLift ιs G ι] [Functor.ShiftLift ιs H ιt] [Functor.ShiftLift ιt I ιs]
  (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)

/-- The unit of a composite of adjunctions commutes with the connecting morphisms if the units
do. -/
instance comp_unit [NatTrans.CommConnecting ι adj₁.unit] [NatTrans.CommConnecting ιs adj₂.unit] :
    NatTrans.CommConnecting ι (adj₁.comp adj₂).unit := by
  have e : (adj₁.comp adj₂).unit = adj₁.unit ≫ Functor.whiskerRight (F.rightUnitor.inv ≫
      Functor.whiskerLeft F adj₂.unit ≫ (Functor.associator _ _ _).inv) G ≫
      (Functor.associator _ _ _).hom := rfl
  rw [e]
  infer_instance

/-- The counit of a composite of adjunctions commutes with the connecting morphisms if the
counits do. -/
instance comp_counit [NatTrans.CommConnecting ιs adj₁.counit]
    [NatTrans.CommConnecting ιt adj₂.counit] :
    NatTrans.CommConnecting ιt (adj₁.comp adj₂).counit := by
  have e : (adj₁.comp adj₂).counit = (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ adj₁.counit ≫ I.rightUnitor.hom) _ ≫ adj₂.counit := rfl
  rw [e]
  infer_instance

end Comp

section SquareTransport

variable {Cv Dv Cw Dw : Type*} [Category Cv] [Category Dv] [Category Cw] [Category Dw]
  [HasShift Dv ℤ] [HasShift Dw ℤ] {ιv : Cv ⥤ Dv} {ιw : Cw ⥤ Dw}
  {G₁ : Cs ⥤ Ct} {G₂ : Ct ⥤ Cu} {G₃ : Cs ⥤ Cv} {G₄ : Cv ⥤ Cu}
  [Functor.ShiftLift ιs G₁ ιt] [Functor.ShiftLift ιt G₂ ιu] [Functor.ShiftLift ιs G₃ ιv]
  [Functor.ShiftLift ιv G₄ ιu]

/-- The transport of an isomorphism commuting with the connecting morphisms commutes with them. -/
instance squareTransport_hom (R : Cx ⥤ Cs) (R' : Cu ⥤ Cw) [Functor.ShiftLift ι R ιs]
    [Functor.ShiftLift ιu R' ιw] (θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄) [NatTrans.CommConnecting ιs θ.hom] :
    NatTrans.CommConnecting ι (Functor.squareTransport R R' θ).hom := by
  dsimp only [Functor.squareTransport, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

end SquareTransport

end NatTrans.CommConnecting

end CategoryTheory
