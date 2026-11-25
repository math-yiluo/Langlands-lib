/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Cocycle lifting with coefficients large enough for morphisms and cover indices

Source: Stacks Project, Cohomology on Sites, Tags 03FC, 03AS, 03F5 and 03AT.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

/-- Lift each product arrow to the enlarged hom universe, keeping its universal property. -/
private def liftCech
    {C : Type u} [Category.{v} C] {T : Type (max v w)} {U : C}
    {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom) :
    SiteCechComplex (C := ULiftHom.{w} C)
      (fun t ↦ ULiftHom.objUp (f t)) (fun t ↦ ULift.up (hom t)) where
  W p t := ULiftHom.objUp (S.W p t)
  pr p t k := ULift.up (S.pr p t k)
  comm p t k := congrArg ULift.up (S.comm p t k)
  universal p t Z a ha := by
    obtain ⟨b, hb, hu⟩ := S.universal p t Z.objDown (fun k ↦ (a k).down)
      (fun k ↦ congrArg ULift.down (ha k))
    refine ⟨ULift.up b, ?_, ?_⟩
    · intro k
      exact congrArg ULift.up (hb k)
    · intro c hc
      exact congrArg ULift.up (hu c.down (fun k ↦ congrArg ULift.down (hc k)))
  W_zero t := congrArg ULiftHom.objUp (S.W_zero t)
  pr_zero t := by
    change (ULiftHom.up (C := C)).map (S.pr 0 t 0) = _
    rw [S.pr_zero, eqToHom_map]
  indexMap t α := ULift.up (S.indexMap t α)
  indexMap_pr t α k := congrArg ULift.up (S.indexMap_pr t α k)

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with hom-universe lifting preserves injectivity, by pulling extension
problems back along the inverse functor and using componentwise monomorphisms. -/
private theorem liftModule_injective
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{max v w})
    (M : PresheafOfModules.{max v w} R) [Injective M] :
    Injective ((PresheafOfModules.pushforward₀
      (ULiftHom.down (C := C) : ULiftHom.{w} C ⥤ C) R).obj M) where
  factors {X Y} g f hf := by
    let P := PresheafOfModules.pushforward₀ (ULiftHom.up (C := C))
      ((ULiftHom.down (C := C)).op ⋙ R)
    have hmono : Mono (P.map f) := PresheafOfModules.mono_of_injective
      (fun Z ↦ PresheafOfModules.injective_of_mono f _)
    let g' : P.obj X ⟶ M := P.map g
    obtain ⟨h, hh⟩ := Injective.factors g' (P.map f)
    refine ⟨{ app Z := h.app (Opposite.op Z.unop.objDown)
              naturality := ?_ }, ?_⟩
    · intro Z Z' a
      exact h.naturality (ULiftHom.down.map a.unop).op
    · apply PresheafOfModules.hom_ext
      intro Z
      exact congrArg (fun k ↦ k.app (Opposite.op Z.unop.objDown)) hh

/-- A positive cocycle in an injective module presheaf has a primitive when its
coefficient universe contains the hom and index universes. No topology is required.
Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC after Tag 03FB,
using Tags 03AS, 03F5 and 03AT.
(blueprint: lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift-max)

Proof: Replace C by ULiftHom.{w} C, whose homs lie in max v w. Precompose R and M
with its down functor. This preserves injectivity: pull an extension problem back
along the up functor, whose component maps preserve monomorphisms, extend into M,
and use the same component maps on the lifted category. Lift the chosen products,
projections and index maps using ULift.up; lift and uniqueness in the original
category prove their universal properties. Apply the existing common-universe
cocycle theorem to this data. Its cochains and alternating restriction differential
reduce to the original ones, so its primitive is the required primitive.
The common-universe theorem implements the free-complex contraction and Yoneda
argument of Tags 03AS, 03F5 and 03AT. This transport does not change coefficient
universes and requires no topology or covering condition; it also covers q=0,
the empty family, and zero coefficients. -/
theorem injective_presheaf_module_cech_cocycle_lift_max
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{max v w})
    (M : PresheafOfModules.{max v w} R) [Injective M]
    {T : Type (max v w)} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (S : SiteCechComplex f hom) (q : ℕ)
    (c : S.cochains M.presheaf (q + 1))
    (hc : S.differentialValue M.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains M.presheaf q, S.differentialValue M.presheaf q b = c := by
  let R' := (ULiftHom.down (C := C) : ULiftHom.{w} C ⥤ C).op ⋙ R
  let M' : PresheafOfModules.{max v w} R' :=
    (PresheafOfModules.pushforward₀ (ULiftHom.down (C := C)) R).obj M
  have : Injective M' := liftModule_injective R M
  exact injective_presheaf_module_cech_cocycle_lift R' M'
    (fun t ↦ ULiftHom.objUp (f t)) (fun t ↦ ULift.up (hom t)) (liftCech S) q c hc

end CategoryTheory
