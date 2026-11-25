/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.RestrictedTensorPullbackStalk

/-! # Tensor pullback preserves a local isomorphism

Source: Stacks Project, Tags 0095 and 0098.
(blueprint: lem-pc-tensor-pullback-local-isomorphism). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A map invertible on U pulls back to a map invertible on its inverse image.
Source: Stacks Project, Tags 0095 and 0098.
(blueprint: lem-pc-tensor-pullback-local-isomorphism).

Proof: At each point x of f inverse-image U, restriction to U identifies the
stalk of h at f(x) with an invertible stalk map. The pullback stalk formula
identifies the stalk of f*(h) with extension of this map along the structure
ring map. Scalar extension sends isomorphisms to isomorphisms. Thus every stalk
map of the restriction of f*(h) is invertible. A map of sheaves of modules is
invertible if it is invertible on all stalks. Empty U has no points and its
restricted category has only zero objects, so the same stalk criterion applies.
No flatness of f or quasi-coherence of the modules is required. -/
theorem tensorPullback_map_over_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) {M N : Y.Modules}
    (h : M ⟶ N) (hh : IsIso (h.over U)) :
    IsIso (((tensorPullback f).map h).over (f ⁻¹ᵁ U)) := by
  classical
  let W := f ⁻¹ᵁ U
  let RY := restrictFunctor U.ι
  let RX := restrictFunctor W.ι
  have : IsIso (RY.map h) := by
    let : IsIso (h.over U) := hh
    have hm : IsIso ((overEquiv U).functor.map (h.over U)) :=
      (overEquiv U).functor.map_isIso (h.over U)
    exact (NatIso.isIso_map_iff (overFunctorEquiv U) h).1 hm
  have hp : IsIso (RX.map ((tensorPullback f).map h)) := by
    apply isIso_of_bijective_stalkLinearMap
    intro x
    let y : U.toScheme := ⟨f x.1, x.2⟩
    have hy : IsIso ((toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (f x.1)).map h) := by
      have : IsIso ((RY ⋙ toPresheaf U.toScheme ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} y).map h) :=
        (toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map_isIso (RY.map h)
      exact (NatIso.isIso_map_iff (restrictStalkNatIso U.ι y) h).1 inferInstance
    have hs : Function.Bijective (h.stalkLinearMap (f x.1)) :=
      ConcreteCategory.bijective_of_isIso
        ((toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (f x.1)).map h)
    let A := (Y.presheaf.stalk (f x.1) : Type u)
    let B := (W.toScheme.presheaf.stalk x : Type u)
    let φ : A →+* B := (f.stalkMap x.1 ≫ W.ι.stalkMap x).hom
    let : Algebra A B := φ.toAlgebra
    obtain ⟨β, hβ⟩ := exists_restricted_tensorPullback_stalk f W x
    have hb : Function.Bijective ((h.stalkLinearMap (f x.1)).baseChange B) :=
      ((LinearEquiv.ofBijective (h.stalkLinearMap (f x.1)) hs).baseChange A B).bijective
    have he : ⇑((RX.map ((tensorPullback f).map h)).stalkLinearMap x) =
        (β N).symm ∘ (h.stalkLinearMap (f x.1)).baseChange B ∘ β M := by
      funext z
      apply (β N).injective
      simp only [Function.comp_apply, AddEquiv.apply_symm_apply]
      exact hβ M N h z
    rw [he]
    exact (β N).symm.bijective.comp (hb.comp (β M).bijective)
  have : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W ⋙
      (overEquiv W).functor).map ((tensorPullback f).map h)) :=
    (NatIso.isIso_map_iff (overFunctorEquiv W) ((tensorPullback f).map h)).2 hp
  have hm : IsIso ((overEquiv W).functor.map
      (((tensorPullback f).map h).over W)) := this
  let : IsIso ((overEquiv W).functor.map
      (((tensorPullback f).map h).over W)) := hm
  exact isIso_of_reflects_iso (((tensorPullback f).map h).over W) (overEquiv W).functor

end AlgebraicGeometry.Scheme.Modules
