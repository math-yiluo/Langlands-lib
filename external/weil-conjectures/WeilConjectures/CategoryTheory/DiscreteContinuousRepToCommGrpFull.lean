/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrp

/-!
# Fullness of the internal group object functor

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
-/

@[expose] public section

universe u w
open CategoryTheory
namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

open scoped CategoryTheory.MonObj
open CartesianMonoidalCategory

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
  [BraidedCategory (DiscreteContAction (Type w) G)]

private lemma discreteRepCommGrp_mul_apply
    (M : DiscreteContinuousRep.{0, u, w} ℤ G)
    {X : DiscreteContAction (Type w) G}
    (s t : X ⟶ (discreteRepCommGrpObject M).X) (x : X.obj.obj.V) :
    (s * t).hom.hom.hom x =
      @Add.add M.obj.V inferInstance (s.hom.hom.hom x) (t.hom.hom.hom x) := by
  let A := (discreteRepCommGrpObject M).X
  change @Add.add M.obj.V inferInstance
    ((fst A A).hom.hom.hom ((lift s t).hom.hom.hom x))
    ((snd A A).hom.hom.hom ((lift s t).hom.hom.hom x)) = _
  have hf := congrArg (fun k : X ⟶ A ↦ k.hom.hom.hom x) (lift_fst s t)
  have hs := congrArg (fun k : X ⟶ A ↦ k.hom.hom.hom x) (lift_snd s t)
  change (fst A A).hom.hom.hom ((lift s t).hom.hom.hom x) = s.hom.hom.hom x at hf
  change (snd A A).hom.hom.hom ((lift s t).hom.hom.hom x) = t.hom.hom.hom x at hs
  rw [hf, hs]


/-- Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-discrete-continuous-rep-to-commgrp-full)

Proof: An internal group morphism gives an equivariant function between the carriers.
The represented group law is pointwise addition. Apply preservation of multiplication
to the two projections from the product representation, then evaluate at any pair (x,y).
This says the underlying function preserves addition. Every additive map of integer
modules is integer-linear, so it gives an equivariant linear map. Its image is the
original internal group morphism because the forgetful functor is faithful.
The zero representation and trivial actions are included; the argument uses no
separation or finiteness assumption on the topological group. -/
theorem discreteContinuousRepToCommGrp_full
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    (discreteContinuousRepToCommGrp (G := G)).Full := by
  constructor
  intro M N f
  let : Module ℤ M.obj.V := M.obj.hV2
  let : Module ℤ N.obj.V := N.obj.hV2
  let : Module ℤ (M.obj.V × M.obj.V) := Prod.instModule
  let P : DiscreteContinuousRep.{0, u, w} ℤ G :=
    ⟨Rep.of (M.obj.ρ.prod M.obj.ρ), by
      intro x
      change IsOpen {g | (M.obj.ρ g x.1, M.obj.ρ g x.2) = x}
      convert (M.property x.1).inter (M.property x.2) using 1
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Prod.ext_iff]⟩
  let p : P ⟶ M := ObjectProperty.homMk
    (Rep.ofHom (Representation.IntertwiningMap.fst ℤ M.obj.ρ M.obj.ρ))
  let q : P ⟶ M := ObjectProperty.homMk
    (Rep.ofHom (Representation.IntertwiningMap.snd ℤ M.obj.ρ M.obj.ρ))
  let X := (discreteContinuousRepToAction G).obj P
  let s : X ⟶ (discreteRepCommGrpObject M).X := (discreteContinuousRepToAction G).map p
  let t : X ⟶ (discreteRepCommGrpObject M).X := (discreteContinuousRepToAction G).map q
  let h : (discreteRepCommGrpObject M).X ⟶ (discreteRepCommGrpObject N).X :=
    (CommGrp.forget (DiscreteContAction (Type w) G)).map f
  let : IsMonHom h := f.hom.hom.isMonHom_hom
  have hadd : ∀ x y : M.obj.V, h.hom.hom.hom (x + y) =
      @Add.add N.obj.V inferInstance (h.hom.hom.hom x) (h.hom.hom.hom y) := by
    intro x y
    have hh := congrArg
      (fun k : (discreteContinuousRepToAction G).obj P ⟶ (discreteRepCommGrpObject N).X ↦
        k.hom.hom.hom (x, y)) (MonObj.mul_comp s t h)
    change h.hom.hom.hom ((s * t).hom.hom.hom (x, y)) =
      ((s ≫ h) * (t ≫ h)).hom.hom.hom (x, y) at hh
    rw [discreteRepCommGrp_mul_apply M, discreteRepCommGrp_mul_apply N] at hh
    exact hh
  let a : M.obj.V →+ N.obj.V :=
    { toFun := fun x ↦ h.hom.hom.hom x
      map_zero' := by
        let z : N.obj.V := h.hom.hom.hom (0 : M.obj.V)
        have hz := hadd 0 0
        rw [add_zero] at hz
        change z = z + z at hz
        exact add_left_cancel (hz.symm.trans (add_zero z).symm)
      map_add' := hadd }
  let b : M.obj ⟶ N.obj := Rep.ofHom
    { toLinearMap := @LinearMap.mk _ _ _ _ _ _ _ _ _ M.obj.hV2 N.obj.hV2 a
        (fun n x ↦ by
          convert! a.map_zsmul n x <;> ext <;> apply int_smul_eq_zsmul)
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (h.hom.hom.comm g) x }
  refine ⟨ObjectProperty.homMk b, ?_⟩
  apply CommGrp.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  rfl

end Rep
