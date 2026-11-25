/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Yoneda

/-!
# Descent data for objects over a base, and the canonical descent datum of a representing object

Let `p : X ⟶ Y` be a morphism in a category `C` and let `V` be an object over `X`. Classically, a
descent datum on `V` relative to `p` is an isomorphism `φ : pr₀^* V ≅ pr₁^* V` over `X ×_Y X`
satisfying the cocycle condition over `X ×_Y X ×_Y X`. By the Yoneda lemma this is the same as a
*transport* of points: for every object `T` and every pair of morphisms `f₁ f₂ : T ⟶ X` with
`f₁ ≫ p = f₂ ≫ p`, a bijection between the `T`-points of `V` lying over `f₁` and those lying over
`f₂`, natural in `T`, trivial for `f₁ = f₂` and compatible with composition. This file uses the
transport form, `CategoryTheory.Over.DescentDatum`, which needs neither fibre products nor the
canonical isomorphisms between iterated pullbacks.

If `F` is a presheaf on `Over Y` and `V` represents the restriction of `F` to `Over X`, then `V`
carries a canonical descent datum: the two pullbacks of `V` to `X ×_Y X` represent the same
restriction of `F`, and the datum is the comparison isomorphism between them. In transport form
it reads: a point of `V` over `f₁` corresponds to an element of `F(T)`, and so does a point of `V`
over `f₂`, because `f₁` and `f₂` define the same object of `Over Y`.

## Main definitions

- `CategoryTheory.Over.DescentDatum`: a descent datum on `V : Over X` relative to `p : X ⟶ Y`
  (blueprint `proposition-jacobian-over-ground-field--1`).
- `CategoryTheory.Over.DescentDatum.IsEffective`: the datum comes from an object over `Y`
  (blueprint `proposition-jacobian-over-ground-field--1`).
- `CategoryTheory.Over.DescentDatum.IsBaseChange`: a descent datum is the base change of
  another one.
- `CategoryTheory.Functor.RepresentableBy.overDescentDatum`: the canonical descent datum on an
  object representing the restriction of a presheaf to `Over X` (blueprint
  `proposition-jacobian-over-ground-field--1`).

## Main statements

- `CategoryTheory.Functor.RepresentableBy.overTransport_overTransport`: the cocycle condition for
  the canonical descent datum (blueprint `proposition-jacobian-over-ground-field--1`).
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace Over

variable {C : Type u} [Category.{v} C] {X Y : C} (p : X ⟶ Y)

/-- A **descent datum** on an object `V` over `X` relative to `p : X ⟶ Y`, in transport form: for
every pair of `T`-points `f₁ f₂ : T ⟶ X` with the same image in `Y`, a map sending the `T`-points
of `V` lying over `f₁` to `T`-points of `V` lying over `f₂`. It is natural in `T`, trivial when
`f₁ = f₂`, and satisfies the cocycle condition; in particular each transport map is a bijection.

By the Yoneda lemma this is the same as an isomorphism `φ : pr₀^* V ≅ pr₁^* V` over `X ×_Y X`
satisfying `pr₀₂^* φ = pr₁₂^* φ ∘ pr₀₁^* φ` over `X ×_Y X ×_Y X` (Stacks 023V): `φ` is the
transport for the universal pair `pr₀, pr₁`.

Mathlib's `CategoryTheory.Pseudofunctor.DescentData` is the same transport-style notion for a
pseudofunctor `F` on `C`: its `hom` compares the pullbacks of the object along any two morphisms
`T ⟶ X` with the same composite to `Y`. It is not used here because there is no pullback
pseudofunctor `X ↦ Over X` available, and the points of `V` are what the descent arguments
below manipulate.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
structure DescentDatum (V : Over X) where
  /-- The transport of points of `V` over `f₁` to points of `V` over `f₂`. -/
  transport {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) : (Over.mk f₁ ⟶ V) → (Over.mk f₂ ⟶ V)
  /-- The transport is natural in `T`. -/
  transport_homMk_comp {T T' : C} (g : T' ⟶ T) (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) :
    transport (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, Category.assoc, h])
      ((Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a) =
      (Over.homMk g : Over.mk (g ≫ f₂) ⟶ Over.mk f₂) ≫ transport f₁ f₂ h a
  /-- The transport along a pair of equal points is the identity. -/
  transport_self {T : C} (f : T ⟶ X) (a : Over.mk f ⟶ V) : transport f f rfl a = a
  /-- The cocycle condition. -/
  transport_transport {T : C} (f₁ f₂ f₃ : T ⟶ X) (h₁₂ : f₁ ≫ p = f₂ ≫ p)
    (h₂₃ : f₂ ≫ p = f₃ ≫ p) (a : Over.mk f₁ ⟶ V) :
    transport f₂ f₃ h₂₃ (transport f₁ f₂ h₁₂ a) = transport f₁ f₃ (h₁₂.trans h₂₃) a

namespace DescentDatum

variable {p} {V : Over X}

/-- A descent datum on `V` relative to `p : X ⟶ Y` is **effective** if `V` is the pullback along
`p` of an object `V₀` over `Y`, through a morphism `q : V ⟶ V₀` which is invariant under the
transport. Equivalently, `V ≅ V₀ ×_Y X` over `X` and the datum is the one induced by `V₀`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
def IsEffective (D : DescentDatum p V) : Prop :=
  ∃ (V₀ : Over Y) (q : V.left ⟶ V₀.left), IsPullback q V.hom V₀.hom p ∧
    ∀ {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q

/-- The transport of a descent datum only depends on the underlying morphisms. -/
lemma transport_left_congr (D : DescentDatum p V) {T : C} {f₁ f₂ f₁' f₂' : T ⟶ X}
    (h : f₁ ≫ p = f₂ ≫ p) (h' : f₁' ≫ p = f₂' ≫ p) (a : Over.mk f₁ ⟶ V)
    (a' : Over.mk f₁' ⟶ V) (e₁ : f₁ = f₁') (e₂ : f₂ = f₂') (ea : a.left = a'.left) :
    (D.transport f₁ f₂ h a).left = (D.transport f₁' f₂' h' a').left := by
  subst e₁ e₂
  obtain rfl : a = a' := Over.OverMorphism.ext ea
  rfl

section Universal

variable [HasPullback (V.hom ≫ p) p]

/-- The universal point for a descent datum on `V`: the first projection
`V ×_Y X ⟶ V`, a point of `V` over `V ×_Y X ⟶ V ⟶ X`. -/
noncomputable abbrev universalPoint :
    Over.mk (pullback.fst (V.hom ≫ p) p ≫ V.hom) ⟶ V :=
  Over.homMk (pullback.fst (V.hom ≫ p) p) rfl

/-- The morphism `φ : V ×_Y X ⟶ V` over `X` underlying a descent datum on `V`: the transport of
the universal point. -/
noncomputable def toHom (D : DescentDatum p V) : Limits.pullback (V.hom ≫ p) p ⟶ V.left :=
  (D.transport _ (pullback.snd (V.hom ≫ p) p) (by rw [Category.assoc, pullback.condition])
    universalPoint).left

/-- **A descent datum is determined by its morphism `φ : V ×_Y X ⟶ V`.** The transport of a
point `a` of `V` over `f₁` to `f₂` is `(a, f₂) ≫ φ`, by naturality of the transport. -/
lemma transport_left_eq_lift_toHom (D : DescentDatum p V) {T : C} (f₁ f₂ : T ⟶ X)
    (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) :
    (D.transport f₁ f₂ h a).left =
      pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h) ≫ D.toHom := by
  let g : T ⟶ Limits.pullback (V.hom ≫ p) p :=
    pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h)
  have key := D.transport_homMk_comp g _ (pullback.snd (V.hom ≫ p) p)
    (by rw [Category.assoc, pullback.condition]) universalPoint
  have e₁ : f₁ = g ≫ pullback.fst (V.hom ≫ p) p ≫ V.hom := by
    rw [pullback.lift_fst_assoc]; exact (Over.w a).symm
  have e₂ : f₂ = g ≫ pullback.snd (V.hom ≫ p) p := (pullback.lift_snd _ _ _).symm
  rw [D.transport_left_congr h (by rw [← e₁, ← e₂]; exact h) a
    ((Over.homMk g rfl : Over.mk (g ≫ pullback.fst (V.hom ≫ p) p ≫ V.hom) ⟶
      Over.mk (pullback.fst (V.hom ≫ p) p ≫ V.hom)) ≫ universalPoint)
    e₁ e₂ (by simp [g]), key]
  rfl

/-- Two descent data on `V` with the same morphism `V ×_Y X ⟶ V` have the same transport. -/
lemma transport_eq_of_toHom_eq {D E : DescentDatum p V} (hDE : D.toHom = E.toHom) {T : C}
    (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) :
    D.transport f₁ f₂ h a = E.transport f₁ f₂ h a :=
  Over.OverMorphism.ext (by
    rw [transport_left_eq_lift_toHom, transport_left_eq_lift_toHom, hDE])


end Universal

/-- A descent datum `D` on `V` relative to `p : X ⟶ Y` **base changes** to a descent datum `E` on
`V'` relative to `p' = ι ≫ p : X' ⟶ Y`, through a morphism `q : V' ⟶ V` over `ι : X' ⟶ X`, if
transporting a point `a` of `V'` by `E` and then mapping it to `V` by `q` is the same as mapping
`a` to `V` and transporting it by `D`:
```
  V'(f₁) --E--> V'(f₂)
    |             |
    q             q
    v             v
  V(f₁ ≫ ι) --D--> V(f₂ ≫ ι)
```
When `q` exhibits `V'` as `V ×_X X'`, this says that `E` is the pullback of `D` along `ι`. -/
def IsBaseChange {X' : C} {ι : X' ⟶ X} {p' : X' ⟶ Y} (hp : ι ≫ p = p') {V' : Over X'}
    {q : V'.left ⟶ V.left} (hq : q ≫ V.hom = V'.hom ≫ ι) (D : DescentDatum p V)
    (E : DescentDatum p' V') : Prop :=
  ∀ ⦃T : C⦄ (f₁ f₂ : T ⟶ X') (h : f₁ ≫ p' = f₂ ≫ p') (a : Over.mk f₁ ⟶ V'),
    (D.transport (f₁ ≫ ι) (f₂ ≫ ι) (by rw [Category.assoc, Category.assoc, hp, h])
      (Over.homMk (a.left ≫ q) (by simp [hq]))).left = (E.transport f₁ f₂ h a).left ≫ q

end DescentDatum

end Over

namespace Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {X Y : C} {p : X ⟶ Y} {F : (Over Y)ᵒᵖ ⥤ Type w}
  {V : Over X} (r : ((Over.map p).op ⋙ F).RepresentableBy V)

/-- The identity of `T`, viewed as a morphism `(T, f₂ ≫ p) ⟶ (T, f₁ ≫ p)` in `Over Y`. -/
abbrev overMapHomMkId {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) :
    (Over.map p).obj (Over.mk f₂) ⟶ (Over.map p).obj (Over.mk f₁) :=
  Over.homMk (𝟙 T) (by simp [h])

/-- The transport of the canonical descent datum of a representing object: a point of `V` over
`f₁` is an element of `F(T, f₁ ≫ p)`, and `(T, f₁ ≫ p) = (T, f₂ ≫ p)` in `Over Y`, so it is
also a point of `V` over `f₂`. -/
def overTransport {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) :
    Over.mk f₂ ⟶ V :=
  r.homEquiv.symm (F.map (overMapHomMkId f₁ f₂ h).op (r.homEquiv a))

lemma homEquiv_overTransport {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) :
    r.homEquiv (r.overTransport f₁ f₂ h a) = F.map (overMapHomMkId f₁ f₂ h).op (r.homEquiv a) :=
  r.homEquiv.apply_symm_apply _

/-- The transport of the canonical descent datum is natural in `T`: for `g : T' ⟶ T`, the square
```
  V(f₁)     --transport-->  V(f₂)
    | g^*                     | g^*
    v                         v
  V(g ≫ f₁) --transport-->  V(g ≫ f₂)
```
commutes, where `V(f)` denotes the points of `V` over `f`. -/
lemma overTransport_homMk_comp {T T' : C} (g : T' ⟶ T) (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) :
    r.overTransport (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, Category.assoc, h])
      ((Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a) =
      (Over.homMk g : Over.mk (g ≫ f₂) ⟶ Over.mk f₂) ≫ r.overTransport f₁ f₂ h a := by
  have e : overMapHomMkId (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, Category.assoc, h]) ≫
      (Over.map p).map (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) =
      (Over.map p).map (Over.homMk g : Over.mk (g ≫ f₂) ⟶ Over.mk f₂) ≫
        overMapHomMkId f₁ f₂ h := by
    ext
    simp
  rw [overTransport, overTransport, r.comp_homEquiv_symm, r.homEquiv_comp]
  congr 1
  have e' := ConcreteCategory.congr_hom (congrArg (fun φ ↦ F.map φ.op) e) (r.homEquiv a)
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at e'
  exact e'

lemma overTransport_self {T : C} (f : T ⟶ X) (a : Over.mk f ⟶ V) :
    r.overTransport f f rfl a = a := by
  have : overMapHomMkId (p := p) f f rfl = 𝟙 _ := by ext; simp
  rw [overTransport, this, op_id, Functor.map_id_apply]
  exact r.homEquiv.symm_apply_apply a

/-- **The cocycle condition is automatic** for the canonical descent datum of a representing
object: both sides are the transport of an element of `F(T)` along the identity of `T`. The
triangle
```
  V(f₁) --transport--> V(f₂)
       \                 |
    transport        transport
          \              v
           ----------> V(f₃)
```
commutes, where `V(f)` denotes the points of `V` over `f`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem overTransport_overTransport {T : C} (f₁ f₂ f₃ : T ⟶ X) (h₁₂ : f₁ ≫ p = f₂ ≫ p)
    (h₂₃ : f₂ ≫ p = f₃ ≫ p) (a : Over.mk f₁ ⟶ V) :
    r.overTransport f₂ f₃ h₂₃ (r.overTransport f₁ f₂ h₁₂ a) =
      r.overTransport f₁ f₃ (h₁₂.trans h₂₃) a := by
  have e : overMapHomMkId f₂ f₃ h₂₃ ≫ overMapHomMkId f₁ f₂ h₁₂ =
      overMapHomMkId f₁ f₃ (h₁₂.trans h₂₃) := by
    ext
    simp
  have e' := ConcreteCategory.congr_hom (congrArg (fun φ ↦ F.map φ.op) e) (r.homEquiv a)
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at e'
  unfold overTransport
  congr 1
  exact (congrArg (F.map (overMapHomMkId f₂ f₃ h₂₃).op) (r.homEquiv.apply_symm_apply _)).trans e'

/-- **The canonical descent datum.** If `V` represents the restriction `(Over.map p).op ⋙ F` of a
presheaf `F` on `Over Y` to `Over X`, then `V` carries a canonical descent datum relative to
`p : X ⟶ Y`: the two pullbacks of `V` to `X ×_Y X` represent the same restriction of `F`, and the
datum is the unique isomorphism between them compatible with the representations. No choice is
involved, which is what makes the datum canonical.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
def overDescentDatum : Over.DescentDatum p V where
  transport := r.overTransport
  transport_homMk_comp := r.overTransport_homMk_comp
  transport_self := r.overTransport_self
  transport_transport := r.overTransport_overTransport

@[simp]
lemma overDescentDatum_transport {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) :
    r.overDescentDatum.transport f₁ f₂ h a = r.overTransport f₁ f₂ h a :=
  rfl

end Functor.RepresentableBy

end CategoryTheory
