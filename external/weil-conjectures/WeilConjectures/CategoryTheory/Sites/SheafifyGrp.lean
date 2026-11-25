/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The group law on the sheafification of a presheaf of groups

Let `G` be a presheaf of groups on a site `(C, J)`. The sheafification of the underlying presheaf
of sets `G ⋙ forget GrpCat` carries a unique group law making the sheafification map a natural
group homomorphism: two sections are multiplied by multiplying local representatives and gluing.
Consequently, an object `X` representing the sheafification is a group object, and the group law
of `X` corresponds to the group law of `G`.

This is used for the relative Picard functor, which is defined as the fppf sheafification of a
presheaf of sets with values in a universe for which Mathlib provides no sheafification of
presheaves of groups.

## Main definitions

- `CategoryTheory.sheafifyGrp`: the sheafification of `G ⋙ forget GrpCat` as a presheaf of groups.
- `CategoryTheory.GrpObj.ofRepresentableBySheafify`: an object representing the sheafification of
  `G ⋙ forget GrpCat` is a group object.

## Main statements

- `CategoryTheory.toSheafify_mul`: the sheafification map is multiplicative.
- `CategoryTheory.homEquiv_symm_toSheafify_mul`: for an object `X` representing the
  sheafification, the map `G(Y) ⟶ (Y ⟶ X)` is multiplicative.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace SheafifyGrp

variable {P : Cᵒᵖ ⥤ Type (max u v)}

/-- The sheafification of `P` is a sheaf of types. -/
lemma isSheaf_sheafify : Presieve.IsSheaf J (sheafify J P) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((presheafToSheaf J _).obj P).property

/-- Two sections of the sheafification which agree on a covering sieve are equal. -/
lemma ext {X : C} {s s' : (sheafify J P).obj (op X)} (R : Sieve X) (hR : R ∈ J X)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → (sheafify J P).map g.op s = (sheafify J P).map g.op s') :
    s = s' :=
  (isSheaf_sheafify.isSeparated R hR).ext fun _ g hg ↦ h g hg

/-- Every section of the sheafification is locally in the image of `P`. -/
lemma imageSieve_mem {X : C} (s : (sheafify J P).obj (op X)) :
    Presheaf.imageSieve (toSheafify J P) s ∈ J X :=
  Presheaf.imageSieve_mem J (toSheafify J P) (U := op X) s

/-- Two sections of `P` with the same image in the sheafification agree locally. -/
lemma equalizerSieve_mem {X : C} {x x' : P.obj (op X)}
    (h : (toSheafify J P).app _ x = (toSheafify J P).app _ x') :
    Presheaf.equalizerSieve (F := P) (X := op X) x x' ∈ J X :=
  Presheaf.equalizerSieve_mem J (toSheafify J P) x x' h

/-- Two sections of the sheafification are equal as soon as they agree after pulling back along
every `g : Y ⟶ X` along which three given sections `a`, `b`, `c` come from `P`. -/
lemma ext_of_imageSieve {X : C} (a b c : (sheafify J P).obj (op X))
    {s s' : (sheafify J P).obj (op X)}
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X) (x y z : P.obj (op Y)),
      (toSheafify J P).app _ x = (sheafify J P).map g.op a →
      (toSheafify J P).app _ y = (sheafify J P).map g.op b →
      (toSheafify J P).app _ z = (sheafify J P).map g.op c →
      (sheafify J P).map g.op s = (sheafify J P).map g.op s') :
    s = s' := by
  refine ext (Presheaf.imageSieve (toSheafify J P) a ⊓ Presheaf.imageSieve (toSheafify J P) b ⊓
    Presheaf.imageSieve (toSheafify J P) c) (J.intersection_covering (J.intersection_covering
      (imageSieve_mem a) (imageSieve_mem b)) (imageSieve_mem c))
      fun Y g ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, ⟨z, hz⟩⟩ ↦ h g x y z hx hy hz

variable (m : ∀ ⦃Y : C⦄, P.obj (op Y) → P.obj (op Y) → P.obj (op Y))
  (hm : ∀ ⦃Y Y' : C⦄ (f : Y' ⟶ Y) (x y : P.obj (op Y)), P.map f.op (m x y) = m (P.map f.op x)
    (P.map f.op y))

include hm in
/-- A natural binary operation on `P` is compatible with the sheafification map. -/
lemma toSheafify_app_eq {Y : C} {x x' y y' : P.obj (op Y)}
    (hx : (toSheafify J P).app _ x = (toSheafify J P).app _ x')
    (hy : (toSheafify J P).app _ y = (toSheafify J P).app _ y') :
    (toSheafify J P).app _ (m x y) = (toSheafify J P).app _ (m x' y') := by
  refine ext _ (J.intersection_covering (equalizerSieve_mem hx) (equalizerSieve_mem hy))
    fun Z g ⟨hgx, hgy⟩ ↦ ?_
  rw [← NatTrans.naturality_apply (toSheafify J P), ← NatTrans.naturality_apply (toSheafify J P),
    hm, hm]
  exact congrArg _ (congrArg₂ _ hgx hgy)

/-- The sections of `P` along `g` defining the family glued to `liftOp m s t`. -/
noncomputable def liftOpFamily {X : C} (s t : (sheafify J P).obj (op X)) :
    Presieve.FamilyOfElements (sheafify J P)
      (Presheaf.imageSieve (toSheafify J P) s ⊓ Presheaf.imageSieve (toSheafify J P) t).arrows :=
  fun _ _ hg ↦ (toSheafify J P).app _ (m hg.1.choose hg.2.choose)

include hm in
lemma liftOpFamily_compatible {X : C} (s t : (sheafify J P).obj (op X)) :
    (liftOpFamily m s t).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  simp only [liftOpFamily]
  rw [← NatTrans.naturality_apply (toSheafify J P), ← NatTrans.naturality_apply (toSheafify J P),
    hm, hm]
  refine toSheafify_app_eq m hm ?_ ?_
  · rw [NatTrans.naturality_apply (toSheafify J P), NatTrans.naturality_apply (toSheafify J P),
      h₁.1.choose_spec, h₂.1.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  · rw [NatTrans.naturality_apply (toSheafify J P), NatTrans.naturality_apply (toSheafify J P),
      h₁.2.choose_spec, h₂.2.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]

/-- The binary operation on the sections of the sheafification of `P` induced by a natural
binary operation `m` on `P`: `s` and `t` are locally images of sections `x` and `y` of `P`, and
`liftOp m s t` is glued from the images of `m x y`. -/
noncomputable def liftOp {X : C} (s t : (sheafify J P).obj (op X)) :
    (sheafify J P).obj (op X) :=
  (isSheaf_sheafify _ (J.intersection_covering (imageSieve_mem s) (imageSieve_mem t))).amalgamate
    (liftOpFamily m s t)
    (liftOpFamily_compatible m hm s t)

/-- **Characterization of `liftOp`.** If `s` and `t` pull back along `g` to the images of `x`
and `y`, then `liftOp m s t` pulls back along `g` to the image of `m x y`. -/
lemma map_liftOp {X Y : C} (s t : (sheafify J P).obj (op X)) (g : Y ⟶ X) (x y : P.obj (op Y))
    (hx : (toSheafify J P).app _ x = (sheafify J P).map g.op s)
    (hy : (toSheafify J P).app _ y = (sheafify J P).map g.op t) :
    (sheafify J P).map g.op (liftOp m hm s t) = (toSheafify J P).app _ (m x y) := by
  have hS := J.intersection_covering (imageSieve_mem s) (imageSieve_mem t)
  refine ext _ (J.pullback_stable g hS) fun Z h hh ↦ ?_
  rw [← Functor.map_comp_apply, ← op_comp, liftOp,
    Presieve.IsSheafFor.valid_glue (f := h ≫ g) (Hf := hh),
    ← NatTrans.naturality_apply (toSheafify J P), hm]
  refine toSheafify_app_eq m hm ?_ ?_
  · rw [hh.1.choose_spec, NatTrans.naturality_apply (toSheafify J P), hx,
      ← Functor.map_comp_apply, ← op_comp]
  · rw [hh.2.choose_spec, NatTrans.naturality_apply (toSheafify J P), hy,
      ← Functor.map_comp_apply, ← op_comp]

end SheafifyGrp

open SheafifyGrp

variable (J) (G : Cᵒᵖ ⥤ GrpCat.{max u v})

/-- The multiplication of the presheaf of groups `G` is natural. -/
lemma map_mul_forget ⦃Y Y' : C⦄ (f : Y' ⟶ Y) (x y : (G ⋙ forget GrpCat).obj (op Y)) :
    (G ⋙ forget GrpCat).map f.op (x * y) =
      (G ⋙ forget GrpCat).map f.op x * (G ⋙ forget GrpCat).map f.op y :=
  map_mul (G.map f.op).hom x y

/-- The inverse of the presheaf of groups `G` is natural. -/
lemma map_inv_forget ⦃Y Y' : C⦄ (f : Y' ⟶ Y) (x : (G ⋙ forget GrpCat).obj (op Y)) :
    (G ⋙ forget GrpCat).map f.op x⁻¹ = ((G ⋙ forget GrpCat).map f.op x)⁻¹ :=
  map_inv (G.map f.op).hom x

/-- The unit of the presheaf of groups `G` is natural. -/
lemma map_one_forget ⦃Y Y' : C⦄ (f : Y' ⟶ Y) :
    (G ⋙ forget GrpCat).map f.op (1 : G.obj (op Y)) = 1 :=
  map_one (G.map f.op).hom

/-- The group law on the sections of the sheafification of `G ⋙ forget GrpCat` over `X`: the
multiplication and the inverse are glued from those of `G` (`SheafifyGrp.liftOp`), and the unit is
the image of the unit of `G`. -/
@[instance_reducible]
noncomputable def sheafifyGroup (X : C) : Group ((sheafify J (G ⋙ forget GrpCat)).obj (op X)) :=
  letI : Mul ((sheafify J (G ⋙ forget GrpCat)).obj (op X)) :=
    ⟨liftOp (fun _ x y ↦ x * y) (map_mul_forget G)⟩
  letI : Inv ((sheafify J (G ⋙ forget GrpCat)).obj (op X)) :=
    ⟨fun s ↦ liftOp (fun _ x _ ↦ x⁻¹) (fun _ _ f x _ ↦ map_inv_forget G f x) s s⟩
  letI : One ((sheafify J (G ⋙ forget GrpCat)).obj (op X)) :=
    ⟨(toSheafify J (G ⋙ forget GrpCat)).app _ (1 : G.obj (op X))⟩
  have hone {Y : C} (g : Y ⟶ X) : (sheafify J (G ⋙ forget GrpCat)).map g.op 1 =
      (toSheafify J (G ⋙ forget GrpCat)).app _ (1 : G.obj (op Y)) := by
    change (sheafify J (G ⋙ forget GrpCat)).map g.op
      ((toSheafify J (G ⋙ forget GrpCat)).app _ (1 : G.obj (op X))) = _
    rw [← NatTrans.naturality_apply (toSheafify J _), map_one_forget]
  have hmul {Y : C} (s t : (sheafify J (G ⋙ forget GrpCat)).obj (op X)) (g : Y ⟶ X) (x y)
      (hx : (toSheafify J (G ⋙ forget GrpCat)).app _ x =
        (sheafify J (G ⋙ forget GrpCat)).map g.op s)
      (hy : (toSheafify J (G ⋙ forget GrpCat)).app _ y =
        (sheafify J (G ⋙ forget GrpCat)).map g.op t) :
      (sheafify J (G ⋙ forget GrpCat)).map g.op (s * t) =
        (toSheafify J (G ⋙ forget GrpCat)).app _ (x * y : G.obj (op Y)) :=
    map_liftOp (fun _ x y ↦ x * y) (map_mul_forget G) s t g x y hx hy
  have hinv {Y : C} (s : (sheafify J (G ⋙ forget GrpCat)).obj (op X)) (g : Y ⟶ X) (x)
      (hx : (toSheafify J (G ⋙ forget GrpCat)).app _ x =
        (sheafify J (G ⋙ forget GrpCat)).map g.op s) :
      (sheafify J (G ⋙ forget GrpCat)).map g.op s⁻¹ =
        (toSheafify J (G ⋙ forget GrpCat)).app _ (x⁻¹ : G.obj (op Y)) :=
    map_liftOp (fun _ x _ ↦ x⁻¹) (fun _ _ f x _ ↦ map_inv_forget G f x) s s g x x hx hx
  { mul_assoc s t r := ext_of_imageSieve s t r fun Y g x y z hx hy hz ↦ by
      rw [hmul _ _ g (x * y) z (hmul _ _ g x y hx hy).symm hz,
        hmul _ _ g x (y * z) hx (hmul _ _ g y z hy hz).symm, _root_.mul_assoc]
    one_mul s := ext_of_imageSieve s s s fun Y g x _ _ hx _ _ ↦ by
      rw [hmul _ _ g 1 x (hone g).symm hx, _root_.one_mul, hx]
    mul_one s := ext_of_imageSieve s s s fun Y g x _ _ hx _ _ ↦ by
      rw [hmul _ _ g x 1 hx (hone g).symm, _root_.mul_one, hx]
    inv_mul_cancel s := ext_of_imageSieve s s s fun Y g x _ _ hx _ _ ↦ by
      rw [hmul _ _ g x⁻¹ x (hinv s g x hx).symm hx, _root_.inv_mul_cancel, hone] }

attribute [local instance] sheafifyGroup

/-- **The multiplication of the sheafification is glued from that of `G`.** If `s` and `t` pull
back along `g` to the images of `x` and `y`, then `s * t` pulls back to the image of `x * y`. -/
lemma map_sheafify_mul {X Y : C} (s t : (sheafify J (G ⋙ forget GrpCat)).obj (op X)) (g : Y ⟶ X)
    (x y : G.obj (op Y))
    (hx : (toSheafify J (G ⋙ forget GrpCat)).app _ x =
      (sheafify J (G ⋙ forget GrpCat)).map g.op s)
    (hy : (toSheafify J (G ⋙ forget GrpCat)).app _ y =
      (sheafify J (G ⋙ forget GrpCat)).map g.op t) :
    (sheafify J (G ⋙ forget GrpCat)).map g.op (s * t) =
      (toSheafify J (G ⋙ forget GrpCat)).app _ (x * y) :=
  map_liftOp (fun _ x y ↦ x * y) (map_mul_forget G) s t g x y hx hy

/-- **The sheafification map is multiplicative.** -/
lemma toSheafify_mul {X : C} (x y : G.obj (op X)) :
    (toSheafify J (G ⋙ forget GrpCat)).app _ (x * y) =
      (toSheafify J (G ⋙ forget GrpCat)).app _ x * (toSheafify J (G ⋙ forget GrpCat)).app _ y := by
  have h := map_sheafify_mul J G ((toSheafify J (G ⋙ forget GrpCat)).app _ x)
    ((toSheafify J (G ⋙ forget GrpCat)).app _ y) (𝟙 X) x y (by simp) (by simp)
  simpa using h.symm

/-- Pulling back sections of the sheafification is multiplicative. -/
lemma sheafify_map_mul {X Y : C} (g : Y ⟶ X) (s t : (sheafify J (G ⋙ forget GrpCat)).obj (op X)) :
    (sheafify J (G ⋙ forget GrpCat)).map g.op (s * t) =
      (sheafify J (G ⋙ forget GrpCat)).map g.op s * (sheafify J (G ⋙ forget GrpCat)).map g.op t :=
  ext_of_imageSieve ((sheafify J (G ⋙ forget GrpCat)).map g.op s)
    ((sheafify J (G ⋙ forget GrpCat)).map g.op t) ((sheafify J (G ⋙ forget GrpCat)).map g.op t)
    fun Z h x y _ hx hy _ ↦ by
      rw [map_sheafify_mul J G _ _ h x y hx hy, ← Functor.map_comp_apply, ← op_comp,
        map_sheafify_mul J G s t (h ≫ g) x y (by rw [op_comp, Functor.map_comp_apply]; exact hx)
          (by rw [op_comp, Functor.map_comp_apply]; exact hy)]

/-- The sheafification of `G ⋙ forget GrpCat`, as a presheaf of groups: the group law on the
sections is `sheafifyGroup`, under which the sheafification map is a natural homomorphism
(`toSheafify_mul`). -/
noncomputable def sheafifyGrp : Cᵒᵖ ⥤ GrpCat.{max u v} where
  obj X := letI := sheafifyGroup J G X.unop
    GrpCat.of ((sheafify J (G ⋙ forget GrpCat)).obj (op X.unop))
  map {X Y} g := GrpCat.ofHom
    { toFun := (sheafify J (G ⋙ forget GrpCat)).map g
      map_one' := by
        change (sheafify J (G ⋙ forget GrpCat)).map g
          ((toSheafify J (G ⋙ forget GrpCat)).app _ (1 : G.obj X)) =
            (toSheafify J (G ⋙ forget GrpCat)).app _ (1 : G.obj Y)
        rw [← NatTrans.naturality_apply (toSheafify J _), ← g.op_unop, map_one_forget]
      map_mul' s t := sheafify_map_mul J G g.unop s t }
  map_id X := by
    ext s
    change (sheafify J (G ⋙ forget GrpCat)).map (𝟙 X) s = s
    simp
  map_comp f g := by
    ext s
    change (sheafify J (G ⋙ forget GrpCat)).map (f ≫ g) s =
      (sheafify J (G ⋙ forget GrpCat)).map g ((sheafify J (G ⋙ forget GrpCat)).map f s)
    simp

/-- The underlying presheaf of sets of `sheafifyGrp J G` is the sheafification of
`G ⋙ forget GrpCat`. -/
lemma sheafifyGrp_comp_forget :
    sheafifyGrp J G ⋙ forget GrpCat = sheafify J (G ⋙ forget GrpCat) :=
  rfl


/-- The group law of the sheafification is commutative if that of `G` is. -/
lemma sheafify_mul_comm (hG : ∀ (X : Cᵒᵖ) (x y : G.obj X), x * y = y * x) {X : C}
    (s t : (sheafify J (G ⋙ forget GrpCat)).obj (op X)) : s * t = t * s :=
  ext_of_imageSieve s t t fun Y g x y _ hx hy _ ↦ by
    rw [map_sheafify_mul J G s t g x y hx hy, map_sheafify_mul J G t s g y x hy hx, hG]

variable [CartesianMonoidalCategory C] {X : C}

variable (X) in
/-- **An object representing the sheafification of a presheaf of groups is a group object.**
Let `X` represent the sheafification of `G ⋙ forget GrpCat`. Then `X` carries the group object
structure for which `(Y ⟶ X) ≃ (sheafify J (G ⋙ forget GrpCat)).obj (op Y)` is a group
isomorphism; see `CategoryTheory.homEquiv_symm_toSheafify_mul`. -/
@[instance_reducible]
noncomputable def GrpObj.ofRepresentableBySheafify
    (α : (sheafify J (G ⋙ forget GrpCat)).RepresentableBy X) : GrpObj X :=
  GrpObj.ofRepresentableBy X (sheafifyGrp J G) α

open scoped MonObj in
/-- The bijection `(Y ⟶ X) ≃ (sheafify J (G ⋙ forget GrpCat)).obj (op Y)` of a representation is
multiplicative for the group object structure `GrpObj.ofRepresentableBySheafify`. -/
lemma homEquiv_mul_ofRepresentableBySheafify
    (α : (sheafify J (G ⋙ forget GrpCat)).RepresentableBy X) {Y : C} (a b : Y ⟶ X) :
    letI := GrpObj.ofRepresentableBySheafify J G X α
    α.homEquiv (a * b) = α.homEquiv a * α.homEquiv b := by
  let := GrpObj.ofRepresentableBySheafify J G X α
  let α' : (sheafifyGrp J G ⋙ forget GrpCat).RepresentableBy X := α
  change α'.homEquiv' (CartesianMonoidalCategory.lift a b ≫ α'.homEquiv'.symm
    (α'.homEquiv' (CartesianMonoidalCategory.fst X X) *
      α'.homEquiv' (CartesianMonoidalCategory.snd X X))) = α'.homEquiv' a * α'.homEquiv' b
  simp only [α'.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← α'.homEquiv'_comp]
  simp

open scoped MonObj in
/-- **The group law of a representing object is the group law of `G`.** For `X` representing
the sheafification of `G ⋙ forget GrpCat`, with the group object structure
`GrpObj.ofRepresentableBySheafify`, the map `G(Y) ⟶ (Y ⟶ X)` sending `x` to the morphism
classifying its image in the sheafification is a group homomorphism. -/
lemma homEquiv_symm_toSheafify_mul
    (α : (sheafify J (G ⋙ forget GrpCat)).RepresentableBy X) {Y : C} (x y : G.obj (op Y)) :
    letI := GrpObj.ofRepresentableBySheafify J G X α
    α.homEquiv.symm ((toSheafify J (G ⋙ forget GrpCat)).app _ (x * y)) =
      α.homEquiv.symm ((toSheafify J (G ⋙ forget GrpCat)).app _ x) *
        α.homEquiv.symm ((toSheafify J (G ⋙ forget GrpCat)).app _ y) := by
  let := GrpObj.ofRepresentableBySheafify J G X α
  apply α.homEquiv.injective
  rw [homEquiv_mul_ofRepresentableBySheafify, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, toSheafify_mul]

open scoped MonObj in
/-- A representing object of the sheafification of a presheaf of commutative groups is a
commutative group object. -/
lemma isCommMonObj_ofRepresentableBySheafify [BraidedCategory C]
    (hG : ∀ (Y : Cᵒᵖ) (x y : G.obj Y), x * y = y * x)
    (α : (sheafify J (G ⋙ forget GrpCat)).RepresentableBy X) :
    letI := GrpObj.ofRepresentableBySheafify J G X α
    IsCommMonObj X := by
  let := GrpObj.ofRepresentableBySheafify J G X α
  refine ⟨?_⟩
  apply α.homEquiv.injective
  have h₁ : (β_ X X).hom ≫ μ[X] = CartesianMonoidalCategory.snd X X *
      CartesianMonoidalCategory.fst X X := by
    rw [Hom.mul_def]
    congr 1
    ext <;> simp
  have h₂ : μ[X] = CartesianMonoidalCategory.fst X X * CartesianMonoidalCategory.snd X X := by
    rw [Hom.mul_def, CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]
  rw [h₁, h₂, homEquiv_mul_ofRepresentableBySheafify, homEquiv_mul_ofRepresentableBySheafify]
  exact sheafify_mul_comm J G hG _ _

end CategoryTheory
