/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Identifying a cokernel of étale sheaves on geometric stalks

Let `f : A ⟶ B` and `d : B ⟶ C` be morphisms of étale sheaves of abelian groups on a scheme
`X` with `f ≫ d = 0`, and let `ψ : P ⟶ C` be a third morphism. If at every geometric point the
stalks satisfy `ker d = im f`, `ψ` is injective and `d` and `ψ` have the same image, then the
cokernel of `f` is isomorphic to `P`: both are identified with the image of `d` inside `C`.

This is how a short exact sequence `0 ⟶ A ⟶ B ⟶ P ⟶ 0` is recognised when the last map is not
directly accessible, but both `B` and `P` map to a common sheaf `C` in which the stalks can be
computed, such as a sheaf of functions on points.

## Main statements

- `AlgebraicGeometry.Scheme.exists_cokernel_iso_hom_comp_eq_of_sheafFiber` and
  `AlgebraicGeometry.Scheme.nonempty_cokernel_iso_of_sheafFiber`: the criterion above.
- `AlgebraicGeometry.Scheme.mono_of_injective_sheafFiber`: a morphism injective on geometric
  stalks is a monomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {A B C P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- A morphism of étale sheaves of abelian groups which is injective on all geometric stalks
is a monomorphism. -/
theorem mono_of_injective_sheafFiber (ψ : P ⟶ C)
    (h : ∀ x : X, Function.Injective ((X.uliftPointSmallEtale x).sheafFiber.map ψ)) :
    Mono ψ := by
  have hmono := (isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyReflectMonomorphisms
    AddCommGrpCat.{u + 1}
  refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _ ψ (fun Φ ↦ ?_)
  obtain ⟨-, ⟨x⟩⟩ := Φ
  exact (AddCommGrpCat.mono_iff_injective _).2 (h x)

/-- **A cokernel identified on geometric stalks.** Let `f : A ⟶ B`, `d : B ⟶ C` and
`ψ : P ⟶ C` be morphisms of étale sheaves of abelian groups with `f ≫ d = 0`. Suppose that at
every geometric point `x̄` of `X` the stalk of `ψ` is injective, the stalks satisfy
`ker d_x̄ = im f_x̄`, and `d_x̄` and `ψ_x̄` have the same image. Then there is an isomorphism
`e : cokernel f ≅ P` through which `ψ` induces the map `cokernel f ⟶ C` given by `d`. -/
theorem exists_cokernel_iso_hom_comp_eq_of_sheafFiber (f : A ⟶ B) (d : B ⟶ C) (ψ : P ⟶ C)
    (w : f ≫ d = 0)
    (h₁ : ∀ (x : X)
      (b : ((X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj B),
      (X.uliftPointSmallEtale x).sheafFiber.map d b = 0 →
        ∃ a, (X.uliftPointSmallEtale x).sheafFiber.map f a = b)
    (h₂ : ∀ x : X, Function.Injective ((X.uliftPointSmallEtale x).sheafFiber.map ψ))
    (h₃ : ∀ (x : X)
      (b : ((X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj B),
      ∃ p, (X.uliftPointSmallEtale x).sheafFiber.map ψ p =
        (X.uliftPointSmallEtale x).sheafFiber.map d b)
    (h₄ : ∀ (x : X)
      (p : ((X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj P),
      ∃ b, (X.uliftPointSmallEtale x).sheafFiber.map d b =
        (X.uliftPointSmallEtale x).sheafFiber.map ψ p) :
    ∃ e : cokernel f ≅ P, e.hom ≫ ψ = cokernel.desc f d w := by
  have hP := isConservativeFamilyOfPoints_ulift_pointSmallEtale X
  have hmono := hP.jointlyReflectMonomorphisms AddCommGrpCat.{u + 1}
  have hfaith := hP.jointlyFaithful AddCommGrpCat.{u + 1}
  let F (x : X) := (X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})
  -- the stalks of the projection onto the cokernel of `f` are surjective
  have hπ (x : X) (z : (F x).obj (cokernel f)) : ∃ b, (F x).map (cokernel.π f) b = z :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance z
  let q := cokernel.desc f d w
  have hq (x : X) (b : (F x).obj B) : (F x).map q ((F x).map (cokernel.π f) b) =
      (F x).map d b := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.π_desc]
  have : Mono q := by
    refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _ q (fun Φ ↦ ?_)
    obtain ⟨-, ⟨x⟩⟩ := Φ
    refine (AddCommGrpCat.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun z hz ↦ ?_)
    obtain ⟨b, rfl⟩ := hπ x z
    change (F x).map q _ = 0 at hz
    rw [hq] at hz
    obtain ⟨a, rfl⟩ := h₁ x b hz
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    rfl
  have : Mono ψ := mono_of_injective_sheafFiber ψ h₂
  have hqψ : q ≫ cokernel.π ψ = 0 := hfaith.map_injective (by
    rintro ⟨-, ⟨x⟩⟩
    rw [Functor.map_zero]
    ext z
    obtain ⟨b, rfl⟩ := hπ x z
    change (F x).map (q ≫ cokernel.π ψ) _ = 0
    rw [Functor.map_comp, ConcreteCategory.comp_apply, hq]
    obtain ⟨p, hp⟩ := h₃ x b
    rw [← hp, ← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero]
    rfl)
  have hψq : ψ ≫ cokernel.π q = 0 := hfaith.map_injective (by
    rintro ⟨-, ⟨x⟩⟩
    rw [Functor.map_zero]
    ext p
    change (F x).map (ψ ≫ cokernel.π q) p = 0
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
    obtain ⟨b, hb⟩ := h₄ x p
    change (F x).map (cokernel.π q) ((F x).map ψ p) = 0
    rw [← hb, ← hq, ← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero]
    rfl)
  refine ⟨⟨Abelian.monoLift ψ q hqψ, Abelian.monoLift q ψ hψq, ?_, ?_⟩,
    Abelian.monoLift_comp ψ q hqψ⟩
  · rw [← cancel_mono q, Category.assoc, Abelian.monoLift_comp, Abelian.monoLift_comp,
      Category.id_comp]
  · rw [← cancel_mono ψ, Category.assoc, Abelian.monoLift_comp, Abelian.monoLift_comp,
      Category.id_comp]

/-- **A cokernel identified on geometric stalks.** Let `f : A ⟶ B`, `d : B ⟶ C` and
`ψ : P ⟶ C` be morphisms of étale sheaves of abelian groups with `f ≫ d = 0`. Suppose that at
every geometric point `x̄` of `X` the stalk of `ψ` is injective, the stalks satisfy
`ker d_x̄ = im f_x̄`, and `d_x̄` and `ψ_x̄` have the same image. Then
`cokernel f ≅ P`. -/
theorem nonempty_cokernel_iso_of_sheafFiber (f : A ⟶ B) (d : B ⟶ C) (ψ : P ⟶ C)
    (w : f ≫ d = 0)
    (h₁ : ∀ (x : X)
      (b : ((X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj B),
      (X.uliftPointSmallEtale x).sheafFiber.map d b = 0 →
        ∃ a, (X.uliftPointSmallEtale x).sheafFiber.map f a = b)
    (h₂ : ∀ x : X, Function.Injective ((X.uliftPointSmallEtale x).sheafFiber.map ψ))
    (h₃ : ∀ (x : X)
      (b : ((X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj B),
      ∃ p, (X.uliftPointSmallEtale x).sheafFiber.map ψ p =
        (X.uliftPointSmallEtale x).sheafFiber.map d b)
    (h₄ : ∀ (x : X)
      (p : ((X.uliftPointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj P),
      ∃ b, (X.uliftPointSmallEtale x).sheafFiber.map d b =
        (X.uliftPointSmallEtale x).sheafFiber.map ψ p) :
    Nonempty (cokernel f ≅ P) :=
  let ⟨e, _⟩ := exists_cokernel_iso_hom_comp_eq_of_sheafFiber f d ψ w h₁ h₂ h₃ h₄
  ⟨e⟩

end AlgebraicGeometry.Scheme
