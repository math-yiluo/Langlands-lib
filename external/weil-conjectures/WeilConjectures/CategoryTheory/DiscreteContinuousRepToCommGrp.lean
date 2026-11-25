/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep

/-!
# Internal group objects associated to discrete continuous integer representations

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
-/

@[expose] public section

universe u w
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Forget the integer-module structure, retaining the discrete continuous action. -/
def discreteContinuousRepToAction :
    DiscreteContinuousRep.{0, u, w} ℤ G ⥤ DiscreteContAction (Type w) G where
  obj M :=
    let A := ((CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).obj
      ((RepToAction ℤ G).obj M.obj)
    ⟨⟨A, by
      let : DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj A) := by
        change @DiscreteTopology M.obj.V ⊥
        exact @discreteTopology_bot M.obj.V
      apply (continuousSMul_iff_stabilizer_isOpen).2
      exact M.property⟩, by
        change @DiscreteTopology M.obj.V ⊥
        exact @discreteTopology_bot M.obj.V⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    (((CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).map
      ((RepToAction ℤ G).map f.hom)))

variable {G}

/-- Equivariant functions into an integer representation form an additive subgroup. -/
def discreteRepEquivariantFunctions
    (M : DiscreteContinuousRep.{0, u, w} ℤ G)
    (X : DiscreteContAction (Type w) G) :
    AddSubgroup (X.obj.obj.V → M.obj.V) where
  carrier := {f | ∀ g x, f (X.obj.obj.ρ g x) = M.obj.ρ g (f x)}
  zero_mem' := by intro g x; exact (map_zero (M.obj.ρ g)).symm
  add_mem' := by
    intro f h hf hh g x
    change f (X.obj.obj.ρ g x) + h (X.obj.obj.ρ g x) = M.obj.ρ g (f x + h x)
    rw [hf, hh, map_add]
  neg_mem' := by
    intro f hf g x
    change -f (X.obj.obj.ρ g x) = M.obj.ρ g (-f x)
    rw [hf, map_neg]

set_option backward.isDefEq.respectTransparency false in
/-- The group-valued presheaf of equivariant functions into a representation. -/
def discreteRepEquivariantPresheaf
    (M : DiscreteContinuousRep.{0, u, w} ℤ G) :
    (DiscreteContAction (Type w) G)ᵒᵖ ⥤ CommGrpCat.{w} where
  obj X := CommGrpCat.of (Multiplicative (discreteRepEquivariantFunctions M X.unop))
  map {X Y} f := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative {
    toFun h := ⟨fun x ↦ h.val (f.unop.hom.hom.hom x), by
      intro g x
      have he := ConcreteCategory.congr_hom (f.unop.hom.hom.comm g) x
      change f.unop.hom.hom.hom ((unop Y).obj.obj.ρ g x) = _ at he
      change h.val (f.unop.hom.hom.hom ((unop Y).obj.obj.ρ g x)) = _
      rw [he]
      exact h.property g _⟩
    map_zero' := rfl
    map_add' _ _ := rfl })
  map_id _ := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro h
    rfl
  map_comp _ _ := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro h
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equivariant functions represent the underlying discrete continuous action. -/
def discreteRepEquivariantRepresentable
    (M : DiscreteContinuousRep.{0, u, w} ℤ G) :
    (discreteRepEquivariantPresheaf M ⋙ CategoryTheory.forget _).RepresentableBy
      ((discreteContinuousRepToAction G).obj M) where
  homEquiv :=
    { toFun f := Multiplicative.ofAdd ⟨fun x ↦ f.hom.hom.hom x, fun g x ↦
        ConcreteCategory.congr_hom (f.hom.hom.comm g) x⟩
      invFun f := ObjectProperty.homMk (ObjectProperty.homMk
        { hom := ↾fun x ↦ f.toAdd.val x
          comm g := by ext x; exact f.toAdd.property g x })
      left_inv f := by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        rfl
      right_inv f := rfl }
  homEquiv_comp _ _ := rfl

variable [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
  [BraidedCategory (DiscreteContAction (Type w) G)]

/-- The internal group law is represented by pointwise addition of equivariant functions. -/
noncomputable def discreteRepCommGrpObject
    (M : DiscreteContinuousRep.{0, u, w} ℤ G) : CommGrp (DiscreteContAction (Type w) G) :=
  letI := CommGrpObj.ofRepresentableBy ((discreteContinuousRepToAction G).obj M)
    (discreteRepEquivariantPresheaf M) (discreteRepEquivariantRepresentable M)
  ⟨(discreteContinuousRepToAction G).obj M⟩

/-- Pointwise addition makes an equivariant linear map an internal group morphism. -/
noncomputable def discreteRepCommGrpMap
    {M N : DiscreteContinuousRep.{0, u, w} ℤ G} (f : M ⟶ N) :
    discreteRepCommGrpObject M ⟶ discreteRepCommGrpObject N := by
  let A := (discreteContinuousRepToAction G).obj M
  let B := (discreteContinuousRepToAction G).obj N
  let h := (discreteContinuousRepToAction G).map f
  refine InducedCategory.homMk (Grp.homMk'' h ?_ ?_)
  · apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext x
    change f.hom.hom (0 : M.obj.V) = 0
    exact map_zero f.hom.hom
  · apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext x
    change f.hom.hom
        (@Add.add M.obj.V inferInstance
          ((fst A A).hom.hom.hom x) ((snd A A).hom.hom.hom x)) =
      @Add.add N.obj.V inferInstance
        ((fst B B).hom.hom.hom ((h ⊗ₘ h).hom.hom.hom x))
        ((snd B B).hom.hom.hom ((h ⊗ₘ h).hom.hom.hom x))
    have hf := congrArg (fun k : A ⊗ A ⟶ B ↦ k.hom.hom.hom x) (tensorHom_fst h h)
    have hs := congrArg (fun k : A ⊗ A ⟶ B ↦ k.hom.hom.hom x) (tensorHom_snd h h)
    change (fst B B).hom.hom.hom ((h ⊗ₘ h).hom.hom.hom x) =
      f.hom.hom ((fst A A).hom.hom.hom x) at hf
    change (snd B B).hom.hom.hom ((h ⊗ₘ h).hom.hom.hom x) =
      f.hom.hom ((snd A A).hom.hom.hom x) at hs
    rw [hf, hs]
    exact map_add f.hom.hom _ _

/-- The reverse functor keeps the underlying action and uses its pointwise group law.
Source: Stacks Project, Tag 04JQ.
(blueprint: def-exc-discrete-continuous-rep-to-commgrp) -/
noncomputable def discreteContinuousRepToCommGrp :
    DiscreteContinuousRep.{0, u, w} ℤ G ⥤ CommGrp (DiscreteContAction (Type w) G) where
  obj := discreteRepCommGrpObject
  map := discreteRepCommGrpMap
  map_id _ := by
    apply CommGrp.hom_ext
    exact (discreteContinuousRepToAction G).map_id _
  map_comp f g := by
    apply CommGrp.hom_ext
    exact (discreteContinuousRepToAction G).map_comp f g

/-- The reverse functor is faithful because it keeps the underlying functions. -/
instance discreteContinuousRepToCommGrp_faithful :
    (discreteContinuousRepToCommGrp (G := G)).Faithful where
  map_injective {M N} f g h := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply DFunLike.ext
    intro x
    have hh := (CommGrp.forget (DiscreteContAction (Type w) G)).congr_map h
    exact congrArg (fun k : (discreteContinuousRepToAction G).obj M ⟶
      (discreteContinuousRepToAction G).obj N ↦ k.hom.hom.hom x) hh

end Rep
