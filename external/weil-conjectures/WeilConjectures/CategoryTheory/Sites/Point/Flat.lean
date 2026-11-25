/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!

# Flatness of sheaves is checked on stalks

Let `(C, J)` be an essentially small site and let `A` be a closed symmetric monoidal
Grothendieck abelian category, for example `ModuleCat Λ` for a commutative ring `Λ`. We show
that a sheaf `F : Sheaf J A` is a flat object (`CategoryTheory.ObjectProperty.flat`: tensoring
with `F` is exact) if and only if its fibre `F_Φ` at every point `Φ` of a conservative family
of points is a flat object of `A`. For the only-if direction `A` is moreover assumed concrete,
so that the fibre of a constant sheaf is its value.

* If every fibre is flat, tensoring with `F` is exact: the fibre functors are exact, strong
  monoidal and jointly reflect isomorphisms, so this follows from
  `CategoryTheory.JointlyReflectIsomorphisms.exactFunctor_of_iso`.
* If `F` is flat and `A` is concrete, then for a monomorphism `f : M ⟶ N` of `A` the map of
  constant sheaves `M_C ⟶ N_C` is a monomorphism, since the constant sheaf functor is left
  exact. Hence so is `F ⊗ M_C ⟶ F ⊗ N_C` and its fibre `F_Φ ⊗ M ⟶ F_Φ ⊗ N` at `Φ`, using that
  the fibre of a constant sheaf is its value
  (`CategoryTheory.GrothendieckTopology.Point.constantSheafCompSheafFiberIso`). As tensoring
  is right exact, `F_Φ` is flat.

The monoidal structure on sheaves is the global instance
`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`.

## Main results

- `CategoryTheory.GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj`: a sheaf whose
  fibres at a family of points jointly reflecting isomorphisms are flat is flat.
- `CategoryTheory.GrothendieckTopology.Point.flat_sheafFiber_obj`: the fibre of a flat sheaf
  at a point is flat.
- `CategoryTheory.GrothendieckTopology.flat_iff_forall_flat_sheafFiber_obj`: a sheaf is flat
  if and only if its fibres at a conservative family of points are flat.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GrothendieckTopology

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}
  {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- **A sheaf with flat fibres is flat.** If the fibre functors of a family `P` of points
jointly reflect isomorphisms of `A`-valued sheaves, then a sheaf whose fibres at all members of
`P` are flat objects of `A` is a flat object. -/
lemma flat_of_forall_flat_sheafFiber_obj {P : ObjectProperty J.Point.{u + 1}}
    (hP : JointlyReflectIsomorphisms fun Φ : P.FullSubcategory ↦ Φ.obj.sheafFiber (A := A))
    (F : Sheaf J A) (hF : ∀ Φ : P.FullSubcategory, ObjectProperty.flat (Φ.obj.sheafFiber.obj F)) :
    ObjectProperty.flat F := by
  -- tensoring with `F` commutes with the fibre functors, which are strong monoidal
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  exact (hP.exactFunctor_of_iso (tensorLeft F) (fun Φ ↦ tensorLeft (Φ.obj.sheafFiber.obj F))
    (fun Φ ↦ (hF Φ).tensorLeft) fun Φ ↦ NatIso.ofComponents
      (fun G ↦ (Functor.Monoidal.μIso Φ.obj.sheafFiber F G).symm)
      fun g ↦ (Functor.OplaxMonoidal.δ_natural_right Φ.obj.sheafFiber F g).symm).1

variable {FA : A → A → Type*} {CA : A → Type (u + 1)} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [hA : ConcreteCategory A FA] [J.WEqualsLocallyBijective A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

namespace Point

variable (Φ : J.Point.{u + 1})

include hA

/-- If the sheaf `F` is flat, then tensoring its fibre `F_Φ` at a point `Φ` with a
monomorphism `f` of `A` gives a monomorphism. -/
lemma mono_sheafFiber_obj_whiskerLeft {F : Sheaf J A} (hF : ObjectProperty.flat F) {M N : A}
    (f : M ⟶ N) [Mono f] : Mono (Φ.sheafFiber.obj F ◁ f) := by
  -- `F_Φ ◁ f` is, up to isomorphism, the fibre of `F ◁ f_C`, where `f_C : M_C ⟶ N_C` is the
  -- map of constant sheaves, a monomorphism since the constant sheaf functor is left exact
  have : PreservesFiniteLimits (tensorLeft F) := hF.tensorLeft.1
  have : Mono (F ◁ (constantSheaf J A).map f) := (tensorLeft F).map_mono _
  have : Mono (Φ.sheafFiber.obj F ◁ Φ.sheafFiber.map ((constantSheaf J A).map f)) := by
    rw [(IsIso.eq_inv_comp _).2 (Functor.OplaxMonoidal.δ_natural_right Φ.sheafFiber F _)]
    infer_instance
  have h : f = (Φ.sheafFiberConstantSheafIso M).inv ≫ Φ.sheafFiber.map ((constantSheaf J A).map f) ≫
      (Φ.sheafFiberConstantSheafIso N).hom := by
    simp [Φ.sheafFiber_map_constantSheaf_map]
  rw [h, whiskerLeft_comp, whiskerLeft_comp]
  infer_instance

/-- **The fibre of a flat sheaf at a point is flat.** -/
lemma flat_sheafFiber_obj {F : Sheaf J A} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat (Φ.sheafFiber.obj F) := by
  -- tensoring with `F_Φ` is right exact, and preserves monomorphisms by
  -- `CategoryTheory.GrothendieckTopology.Point.mono_sheafFiber_obj_whiskerLeft`
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  refine ((Functor.preservesFiniteLimits_tfae _).out 1 4).1 fun S hS ↦ ?_
  have := hS.mono_f
  refine ⟨?_, Φ.mono_sheafFiber_obj_whiskerLeft hF S.f⟩
  exact ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1 inferInstance S hS).1

end Point

variable [J.HasSheafCompose (CategoryTheory.forget A)]

include hA

/-- **Flatness of sheaves is checked on stalks.** A sheaf is flat if and only if its fibres at
all points of a conservative family of points are flat. -/
theorem flat_iff_forall_flat_sheafFiber_obj {P : ObjectProperty J.Point.{u + 1}}
    (hP : P.IsConservativeFamilyOfPoints) (F : Sheaf J A) :
    ObjectProperty.flat F ↔
      ∀ Φ : P.FullSubcategory, ObjectProperty.flat (Φ.obj.sheafFiber.obj F) :=
  ⟨fun hF Φ ↦ Φ.obj.flat_sheafFiber_obj hF,
    flat_of_forall_flat_sheafFiber_obj (hP.jointlyReflectIsomorphisms A) F⟩

end CategoryTheory.GrothendieckTopology
