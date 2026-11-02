/-
Adapted from `Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: generalized from the base `Spec R` of a commutative ring `R` to an arbitrary base
scheme `S`, with the namespace `GoodReductionJacobian` renamed `GroupLawOverBase`; FLT
commands from `P2M.Util` are replaced by standard Lean commands. The paired Markdown file
lists all changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj


namespace GroupLawOverBase

def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩

@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl

structure RelativeGroupLaw (S : Scheme.{u}) {A : Scheme.{u}}
    (f : A ⟶ S) where

  mul : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f

  one : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t f

  inv : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    SchemeHomOver t f → SchemeHomOver t f

  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)

  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t f),
    mul t (one t) x = x

  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t f),
    mul t x (one t) = x

  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (x : SchemeHomOver t f), mul t (inv t x) x = one t

  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ S)
    (t' : T' ⟶ S) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)

namespace RelativeGroupLaw

def IsCommutative {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x

theorem IsCommutative.mul_comm {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} {G : RelativeGroupLaw S f} (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x :=
  hc t x y

@[reducible]
def pointGroup {S : Scheme.{u}} {A : Scheme.{u}} {f : A ⟶ S}
    (G : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ S) :
    Group (SchemeHomOver t f) where
  mul x y := G.mul t x y
  one := G.one t
  inv x := G.inv t x
  mul_assoc := G.mul_assoc t
  one_mul := G.one_mul t
  mul_one := G.mul_one t
  inv_mul_cancel := G.inv_mul_cancel t

theorem mul_inv_cancel {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ S) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by
        rw [G.inv_mul_cancel t (G.inv t x)]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.inv t x) (G.mul t x (G.inv t x))) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.mul t (G.inv t x) x) (G.inv t x)) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.one t) (G.inv t x)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t (G.inv t x)) (G.inv t x) := by rw [G.one_mul]
    _ = G.one t := G.inv_mul_cancel t (G.inv t x)

theorem one_natural {S : Scheme.{u}} {A : Scheme.{u}}
    {f : A ⟶ S} (G : RelativeGroupLaw S f) {T T' : Scheme.{u}}
    (t : T ⟶ S) (t' : T' ⟶ S)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t)) =
      schemeHomOverComp ψ hψ (G.one t) := by
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  calc schemeHomOverComp ψ hψ (G.one t)
      = G.mul t' (G.one t') (schemeHomOverComp ψ hψ (G.one t)) := (G.one_mul t' _).symm
    _ = G.mul t' (G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t))) (schemeHomOverComp ψ hψ (G.one t)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t))) := by
        rw [G.mul_assoc]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t)) := by rw [h]
    _ = G.one t' := G.inv_mul_cancel t' _

end RelativeGroupLaw

def trivialRelativeGroupLaw (S : Scheme.{u}) :
    RelativeGroupLaw S (𝟙 (S)) where
  mul := fun _ x _ => x
  one := fun t => ⟨t, Category.comp_id t⟩
  inv := fun _ x => x
  mul_assoc := fun _ _ _ _ => rfl
  one_mul := fun t _ =>
    (subsingleton_schemeHomOver_of_isIso t (𝟙 (S))).allEq _ _
  mul_one := fun _ _ => rfl
  inv_mul_cancel := fun t _ =>
    (subsingleton_schemeHomOver_of_isIso t (𝟙 (S))).allEq _ _
  mul_natural := fun _ _ _ _ _ _ => rfl

theorem relativeGroupLaw_pointwise_eq_of_isIso {S : Scheme.{u}} {A : Scheme.{u}}
    (f : A ⟶ S) [IsIso f]
    (G G' : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ S)
    (x y : SchemeHomOver t f) :
    G.mul t x y = G'.mul t x y ∧ G.one t = G'.one t ∧ G.inv t x = G'.inv t x :=
  ⟨(subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _⟩

end GroupLawOverBase
