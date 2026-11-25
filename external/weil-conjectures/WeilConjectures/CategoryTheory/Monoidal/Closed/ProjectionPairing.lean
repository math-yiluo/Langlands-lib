/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Perfectness of a pairing built from a projection map

Let `D` be a monoidal closed category with a shift by `ℤ`, let `R` be an object of `D`, and let
`π : R ⊗ - ⟶ P ⋙ F` be a natural transformation, for functors `P : D ⥤ C` and `F : C ⥤ D`
commuting with shifts. Given `M : D`, maps `c : P M ⟶ V`, `w : V ⟶ W` in `C` and a "trace"
`t : F(W[n]) ⟶ 𝟙_ D`, the composite
```
R ⊗ M[n] ≅ (R ⊗ M)[n] ──π[n]──▶ (F (P M))[n] ──F(c ≫ w)[n]──▶ (F W)[n] ≅ F(W[n]) ──t──▶ 𝟙_ D
```
is a pairing `R ⊗ M[n] ⟶ 𝟙_ D`. This file shows that it is *perfect* — its adjoint
`M[n] ⟶ [R, 𝟙_ D]` is an isomorphism — as soon as `π` is an isomorphism on a class of test
objects detecting isomorphisms, `h ↦ P h ≫ c ≫ w` is a bijection `(N ⟶ M) ≃ (P N ⟶ W)` and
`z ↦ F(z[n]) ≫ t` is a bijection `(U ⟶ W) ≃ (F(U[n]) ⟶ 𝟙_ D)`
(`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`).

This is the formal core of the statement that the derived Poincaré pairing is perfect: there
`π` is the projection map of `Ra_!`, `P = La^* ⋙ (K ⊗ᴸ -)`, `c` is induced by the counit of
`La^* ⊣ Ra_*`, `w` is the evaluation, and `t` is the trace of `Ra_! ⊣ Ra^!` read through an
orientation.

## Implementation notes

The instances on `C` and `D` are taken as implicit arguments rather than instance arguments, so
that applying the theorem to a concrete pairing determines them by unification with that
pairing. This keeps the instances that the kernel has to compare syntactically equal.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open Category MonoidalCategory

variable {C D : Type*} [Category C] [Category D]

/-- A pairing `R ⊗ M[n] ⟶ 𝟙_ D` assembled from a projection map `π : R ⊗ - ⟶ P ⋙ F`, maps
`c : P M ⟶ V`, `w : V ⟶ W` and a trace `t : F(W[n]) ⟶ 𝟙_ D` is perfect, provided that

* `π` is an isomorphism at every object of a class `S` such that a morphism `u` is an
  isomorphism as soon as composition with `u` is bijective on morphisms out of `N[n]` for
  all `N` in `S`;
* `h ↦ P h ≫ c ≫ w` is a bijection `(N ⟶ M) ≃ (P N ⟶ W)` for all `N`;
* `z ↦ F(z[n]) ≫ t` is a bijection `(U ⟶ W) ≃ (F(U[n]) ⟶ 𝟙_ D)` for all `U`.

Write `β` for the pairing. The proof checks that for `N` in `S` the square
```
            h ↦ h[n] ≫ curry β
(N ⟶ M) ─────────────────────────▶ (N[n] ⟶ [R, 𝟙_ D])
   │                                         ▲
   │ h ↦ P h ≫ c ≫ w                         │ curry
   ▼                                         │
(P N ⟶ W) ──▶ (F(P N[n]) ⟶ 𝟙_ D) ──▶ (R ⊗ N[n] ⟶ 𝟙_ D)
     f ↦ F(f[n]) ≫ t        v ↦ (π_N)[n] ≫ v
```
commutes (with the shift isomorphisms of `R ⊗ -` and `F` absorbed in the bottom right map), so
that the top map is a bijection; as `h ↦ h[n]` is a bijection, composition with `curry β` is
bijective on morphisms out of `N[n]`. -/
theorem isIso_curry_of_projection {_ : HasShift C ℤ} {_ : HasShift D ℤ}
    {_ : MonoidalCategory D} {_ : MonoidalClosed D} (R : D)
    {_ : ((curriedTensor D).obj R).CommShift ℤ}
    (P : D ⥤ C) (F : C ⥤ D) {_ : F.CommShift ℤ}
    (π : (curriedTensor D).obj R ⟶ P ⋙ F) (n : ℤ) (M : D) {V W : C}
    (c : P.obj M ⟶ V) (w : V ⟶ W) (t : F.obj (W⟦n⟧) ⟶ 𝟙_ D)
    (S : D → Prop)
    (hdet : ∀ ⦃X Y : D⦄ (u : X ⟶ Y),
      (∀ N, S N → Function.Bijective (fun g : N⟦n⟧ ⟶ X ↦ g ≫ u)) → IsIso u)
    (hπ : ∀ N, S N → IsIso (π.app N))
    (hc : ∀ N, Function.Bijective (fun h : N ⟶ M ↦ P.map h ≫ c ≫ w))
    (ht : ∀ U, Function.Bijective (fun z : U ⟶ W ↦ F.map (z⟦n⟧') ≫ t)) :
    IsIso (curry ((((curriedTensor D).obj R).commShiftIso n).hom.app M ≫
      ((π.app M ≫ F.map c) ≫ F.map w)⟦n⟧' ≫ (F.commShiftIso n).inv.app W ≫ t)) := by
  apply hdet
  intro N hN
  have := hπ N hN
  have hshift : Function.Bijective (fun h : N ⟶ M ↦ h⟦n⟧') :=
    ⟨(shiftFunctor D n).map_injective, (shiftFunctor D n).map_surjective⟩
  rw [← Function.Bijective.of_comp_iff _ hshift]
  have key : ∀ h : N ⟶ M, h⟦n⟧' ≫ curry
      ((((curriedTensor D).obj R).commShiftIso n).hom.app M ≫
      ((π.app M ≫ F.map c) ≫ F.map w)⟦n⟧' ≫ (F.commShiftIso n).inv.app W ≫ t) =
      curry ((((curriedTensor D).obj R).commShiftIso n).hom.app N ≫ (π.app N)⟦n⟧' ≫
        (F.commShiftIso n).inv.app (P.obj N) ≫ F.map ((P.map h ≫ c ≫ w)⟦n⟧') ≫ t) := by
    intro h
    rw [← curry_natural_left]
    congr 1
    have e₁ : ((curriedTensor D).obj R).map h ≫ (π.app M ≫ F.map c) ≫ F.map w =
        π.app N ≫ F.map (P.map h ≫ c ≫ w) := by
      rw [← Category.assoc, ← Category.assoc, π.naturality h]
      simp
    have e₂ : ∀ f : P.obj N ⟶ W, (π.app N ≫ F.map f)⟦n⟧' ≫
        (F.commShiftIso n).inv.app W ≫ t =
        (π.app N)⟦n⟧' ≫ (F.commShiftIso n).inv.app _ ≫ F.map (f⟦n⟧') ≫ t := by
      intro f
      simp [Functor.commShiftIso_inv_naturality_assoc]
    change ((curriedTensor D).obj R).map (h⟦n⟧') ≫ _ = _
    rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc, e₁, e₂]
  have hcomp : (fun h : N ⟶ M ↦ h⟦n⟧' ≫ curry
      ((((curriedTensor D).obj R).commShiftIso n).hom.app M ≫
        ((π.app M ≫ F.map c) ≫ F.map w)⟦n⟧' ≫ (F.commShiftIso n).inv.app W ≫ t)) =
      curry ∘ (fun v ↦ ((((curriedTensor D).obj R).commShiftIso n).hom.app N ≫
          (π.app N)⟦n⟧' ≫ (F.commShiftIso n).inv.app (P.obj N)) ≫ v) ∘
        (fun z ↦ F.map (z⟦n⟧') ≫ t) ∘ (fun h ↦ P.map h ≫ c ≫ w) := by
    funext h
    rw [key]
    simp only [Function.comp_apply, Category.assoc]
  change Function.Bijective (fun h : N ⟶ M ↦ h⟦n⟧' ≫ curry _)
  rw [hcomp]
  exact Function.Bijective.comp ⟨curry_injective, fun g ↦ ⟨uncurry g, curry_uncurry g⟩⟩
    (((isIso_iff_coyoneda_map_bijective _).1 inferInstance _).comp ((ht _).comp (hc _)))

end CategoryTheory.MonoidalClosed
