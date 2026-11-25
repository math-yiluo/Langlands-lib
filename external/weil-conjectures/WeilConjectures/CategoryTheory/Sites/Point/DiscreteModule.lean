/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.Point.GroupAction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import WeilConjectures.RepresentationTheory.DiscreteModule.Transport

/-!
# Sheaves on a site with a Galois point and discrete modules

Let `Φ` be a point of a site `(C, J)` and let a topological group `G` act on its fibre functor.
Suppose that

* the fibre of every abelian sheaf, with its action of `G`, is a discrete `G`-module;
* for every discrete `G`-module `M`, the counit `(Φ.equivariantSheaf M)_Φ ⟶ M` is an
  isomorphism;
* the fibre functor at `Φ` reflects isomorphisms.

We call this a *Galois point* (`CategoryTheory.GrothendieckTopology.Point.IsGaloisPoint`). Then
the fibre functor is an equivalence of categories between abelian sheaves on `(C, J)` and
discrete `G`-modules, with quasi-inverse the sheaf of equivariant maps, and it identifies sheaf
cohomology with continuous cohomology: `Hⁿ(C, F) ≃ Hⁿ(G, F_Φ)`. In degree `0` this says that
global sections are the invariants of the fibre.

The prime example is the spectrum of a field `K` with the geometric point given by a separable
closure, and `G` the absolute Galois group of `K`.

## Main definitions and statements

- `CategoryTheory.GrothendieckTopology.Point.IsGaloisPoint.equivalence`: the equivalence of
  categories `Sheaf J Ab ≌ DiscreteModule G`.
- `CategoryTheory.GrothendieckTopology.Point.IsGaloisPoint.sheafHAddEquiv`: the isomorphism
  `Hⁿ(C, F) ≃ Hⁿ(G, F_Φ)`.
- `CategoryTheory.GrothendieckTopology.Point.IsGaloisPoint.sheafHZeroAddEquiv`: the isomorphism
  `H⁰(C, F) ≃ (F_Φ)ᴳ`.
-/

@[expose] public section

universe w' w v u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Type u'} [Group G]
  [TopologicalSpace G] (Φ : Point.{max u' w} J) (act : G →* End Φ.fiber)

/-- A point `Φ` with an action of a topological group `G` on its fibre functor is a *Galois
point* if the fibres of abelian sheaves are discrete `G`-modules, the counit of the adjunction
`Φ.sheafFiberActionAdjunction` is an isomorphism on discrete modules, and the fibre functor
reflects isomorphisms. -/
structure IsGaloisPoint : Prop where
  isDiscreteModule (F : Sheaf J AddCommGrpCat.{max u' w}) :
    Action.IsDiscreteModule.{max u' w} ((Φ.sheafFiberAction act).obj F)
  isIso_fromEquivariantSheaf (M : DiscreteModule.{w} G) :
    IsIso (Φ.fromEquivariantSheaf act M.obj)
  isIso_of_isIso_sheafFiber_map {F F' : Sheaf J AddCommGrpCat.{max u' w}} (f : F ⟶ F') :
    IsIso (Φ.sheafFiber.map f) → IsIso f

namespace IsGaloisPoint

variable {Φ act} (h : Φ.IsGaloisPoint act)
include h

/-- The fibre functor at a Galois point, with values in discrete modules. -/
noncomputable def functor : Sheaf J AddCommGrpCat.{max u' w} ⥤ DiscreteModule.{w} G :=
  ObjectProperty.lift _ (Φ.sheafFiberAction act) h.isDiscreteModule

lemma isIso_toEquivariantSheaf (F : Sheaf J AddCommGrpCat.{max u' w}) :
    IsIso (Φ.toEquivariantSheaf act F) := by
  refine h.isIso_of_isIso_sheafFiber_map _ ?_
  have := h.isIso_fromEquivariantSheaf ⟨_, h.isDiscreteModule F⟩
  have h₁ : (Φ.sheafFiberAction act).map (Φ.toEquivariantSheaf act F) ≫
      Φ.fromEquivariantSheaf act ((Φ.sheafFiberAction act).obj F) = 𝟙 _ :=
    (Φ.sheafFiberActionAdjunction act).left_triangle_components F
  have : IsIso ((Φ.sheafFiberAction act).map (Φ.toEquivariantSheaf act F) ≫
      Φ.fromEquivariantSheaf act ((Φ.sheafFiberAction act).obj F)) := by
    rw [h₁]
    infer_instance
  have : IsIso ((Φ.sheafFiberAction act).map (Φ.toEquivariantSheaf act F)) :=
    IsIso.of_isIso_comp_right _ (Φ.fromEquivariantSheaf act ((Φ.sheafFiberAction act).obj F))
  exact (inferInstance : IsIso ((Action.forget _ _).map
    ((Φ.sheafFiberAction act).map (Φ.toEquivariantSheaf act F))))

/-- **Sheaves and discrete modules.** At a Galois point, the fibre functor is an equivalence
of categories between abelian sheaves and discrete `G`-modules, with quasi-inverse the sheaf of
equivariant maps. -/
noncomputable def equivalence : Sheaf J AddCommGrpCat.{max u' w} ≌ DiscreteModule.{w} G :=
  Equivalence.mk h.functor (ObjectProperty.ι _ ⋙ Φ.equivariantSheafFunctor act)
    (NatIso.ofComponents
      (fun F ↦ have := h.isIso_toEquivariantSheaf F; asIso (Φ.toEquivariantSheaf act F))
      fun f ↦ (Φ.sheafFiberActionAdjunction act).unit.naturality f)
    (NatIso.ofComponents
      (fun M ↦ have := h.isIso_fromEquivariantSheaf M
        ObjectProperty.isoMk _ (asIso (Φ.fromEquivariantSheaf act M.obj)))
      fun f ↦ ObjectProperty.hom_ext _
        ((Φ.sheafFiberActionAdjunction act).counit.naturality f.hom))

@[simp]
lemma equivalence_functor : h.equivalence.functor = h.functor :=
  rfl

lemma additive_equivalence_functor : h.equivalence.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable [IsTopologicalGroup G] [HasSheafify J AddCommGrpCat.{max u' w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' w}] [LocallySmall.{max u' w} C]

/-- The fibre of the constant sheaf with value `A` is the trivial module `A`. -/
noncomputable def functorObjConstantSheafIso (A : AddCommGrpCat.{max u' w}) :
    h.functor.obj ((constantSheaf J AddCommGrpCat.{max u' w}).obj A) ≅
      DiscreteModule.trivial.{w} G A :=
  ObjectProperty.isoMk _ (Φ.sheafFiberActionConstantSheafIso act A)

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max u' w})]

/-- **Sheaf cohomology at a Galois point is continuous cohomology**: `Hⁿ(C, F) ≃ Hⁿ(G, F_Φ)`,
since an exact equivalence of abelian categories identifies `Ext`-groups. -/
noncomputable def sheafHAddEquiv (F : Sheaf J AddCommGrpCat.{max u' w}) (n : ℕ) :
    Sheaf.H F n ≃+ DiscreteModule.H G (h.functor.obj F) n :=
  haveI := h.additive_equivalence_functor
  (Abelian.Ext.postcompAddEquiv _ (h.equivalence.unitIso.app F) n).trans <|
    (h.equivalence.toAdjunction.extAddEquiv _ (h.functor.obj F) n).trans <|
      Abelian.Ext.precompAddEquiv (h.functorObjConstantSheafIso _).symm _ n

/-- At a Galois point, global sections are the invariants of the fibre:
`H⁰(C, F) ≃ (F_Φ)ᴳ`. -/
noncomputable def sheafHZeroAddEquiv (F : Sheaf J AddCommGrpCat.{max u' w}) :
    Sheaf.H F 0 ≃+ (DiscreteModule.invariants G).obj (h.functor.obj F) :=
  (h.sheafHAddEquiv F 0).trans (DiscreteModule.H_zero_addEquiv _)

/-- At a Galois point, the cohomology of the constant sheaf with value `A` is the continuous
cohomology of the trivial module `A`. -/
noncomputable def sheafHConstantSheafAddEquiv (A : AddCommGrpCat.{max u' w}) (n : ℕ) :
    Sheaf.H ((constantSheaf J AddCommGrpCat.{max u' w}).obj A) n ≃+
      DiscreteModule.H G (DiscreteModule.trivial.{w} G A) n :=
  (h.sheafHAddEquiv _ n).trans
    (Abelian.Ext.postcompAddEquiv _ (h.functorObjConstantSheafIso A) n)

end IsGaloisPoint

end CategoryTheory.GrothendieckTopology.Point
