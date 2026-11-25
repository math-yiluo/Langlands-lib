/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Pullback of finite étale schemes and local Frobenius elements

This file provides two constructions on the category `FÉt(Y)` of finite étale `Y`-schemes and
its fibre functors.

* For a morphism `f : X ⟶ Y`, base change `P ↦ P ×_Y X` is a functor
  `AlgebraicGeometry.Scheme.FiniteEtale.pullback f : FÉt(Y) ⥤ FÉt(X)`. For an open immersion
  `j : U ⟶ C` it is restriction of finite étale covers to `U`, which induces the map
  `π₁(U) → π₁(C)` on fundamental groups.
* An automorphism `e` of `Spec Ω` over a geometric point `s : Spec Ω ⟶ Y` acts on the fibre
  functor at `s` by precomposition (`AlgebraicGeometry.Scheme.FiniteEtale.fiberPrecompIso`).
  For a point `x` of `Y` with finite residue field `κ(x)`, the geometric point
  `x̄ : Spec κ(x)‾ ⟶ Y` and the inverse `σ_x⁻¹` of the arithmetic Frobenius
  `σ_x : a ↦ a ^ #κ(x)` of `κ(x)‾` give the *geometric Frobenius* `F_x` at `x`, an automorphism
  of the fibre functor at `x̄` (`AlgebraicGeometry.Scheme.FiniteEtale.geometricFrobeniusAt`).

An element `g` of a fundamental group `G = π₁(Y, s)` is a *Frobenius element at `x`*
(`AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement`) if it acts on the fibre functor at
`s` as `F_x`, transported along some isomorphism of fibre functors (a "path") from `x̄` to `s`.
Changing the path conjugates `g`, so this defines the Frobenius conjugacy class at `x`
(blueprint `definition-weil-representation--1`). On the geometric fibre `Hom_{k₀}(A, Ω)` of a
constant cover `Y ×_{k₀} Spec A` the element `F_x` acts as the `[κ(x) : k₀]`-th power of the
geometric Frobenius of `k₀`.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.pullback`
- `AlgebraicGeometry.Scheme.FiniteEtale.fiberPrecompIso`
- `AlgebraicGeometry.Scheme.FiniteEtale.geometricFrobeniusAt`
- `AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement`
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change `P ↦ P ×_Y X` of finite étale schemes along a morphism `f : X ⟶ Y`, as a functor
`FÉt(Y) ⥤ FÉt(X)`. -/
noncomputable def pullback (f : X ⟶ Y) : Y.FiniteEtale ⥤ X.FiniteEtale where
  obj P := ⟨MorphismProperty.Over.mk ⊤ (Limits.pullback.snd P.obj.hom f)
      (by have : Etale P.obj.hom := P.obj.prop; infer_instance),
    by have : IsFinite P.obj.hom := P.property
       exact inferInstanceAs (IsFinite (Limits.pullback.snd P.obj.hom f))⟩
  map {P Q} φ := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.map P.obj.hom f Q.obj.hom f φ.hom.left (𝟙 X) (𝟙 Y)
      ((Category.comp_id _).trans (hom_left_comp φ).symm) (by simp))
    (by exact (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)))
  map_id P := by
    apply hom_ext
    change Limits.pullback.map _ _ _ _ (𝟙 _) (𝟙 X) (𝟙 Y)
      ((Category.comp_id _).trans (hom_left_comp (𝟙 P)).symm) (by simp) = 𝟙 _
    apply Limits.pullback.hom_ext <;> simp
  map_comp {P Q R} φ ψ := by
    apply hom_ext
    change Limits.pullback.map _ _ _ _ (φ.hom.left ≫ ψ.hom.left) (𝟙 X) (𝟙 Y)
        ((Category.comp_id _).trans (hom_left_comp (φ ≫ ψ)).symm) (by simp) =
      Limits.pullback.map _ _ _ _ φ.hom.left (𝟙 X) (𝟙 Y)
          ((Category.comp_id _).trans (hom_left_comp φ).symm) (by simp) ≫
        Limits.pullback.map _ _ _ _ ψ.hom.left (𝟙 X) (𝟙 Y)
          ((Category.comp_id _).trans (hom_left_comp ψ).symm) (by simp)
    apply Limits.pullback.hom_ext <;> simp

@[simp]
lemma pullback_obj_obj_hom (P : Y.FiniteEtale) :
    ((pullback f).obj P).obj.hom = Limits.pullback.snd P.obj.hom f :=
  rfl

@[simp]
lemma pullback_map_hom_left {P Q : Y.FiniteEtale} (φ : P ⟶ Q) :
    ((pullback f).map φ).hom.left =
      Limits.pullback.map P.obj.hom f Q.obj.hom f φ.hom.left (𝟙 X) (𝟙 Y)
        ((Category.comp_id _).trans (hom_left_comp φ).symm) (by simp) :=
  rfl

end Pullback

section Frobenius

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- An automorphism `e` of `Spec Ω` over the geometric point `s : Spec Ω ⟶ Y` acts on the
geometric fibre `Hom_Y(Spec Ω, P)` of every finite étale `Y`-scheme `P` by precomposition,
`y ↦ e ≫ y`, naturally in `P`: it is an automorphism of the fibre functor at `s`. -/
noncomputable def fiberPrecompIso (e : Spec (.of Ω) ≅ Spec (.of Ω)) (he : e.hom ≫ s = s) :
    fiber s ≅ fiber s :=
  NatIso.ofComponents
    (fun P ↦ FintypeCat.equivEquivIso
      { toFun y := Over.homMk (U := Over.mk s) (e.hom ≫ y.left)
          ((Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) (fiber_left_comp s y)).trans he))
        invFun y := Over.homMk (U := Over.mk s) (e.inv ≫ y.left)
          ((Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) (fiber_left_comp s y)).trans
            ((congrArg (e.inv ≫ ·) he.symm).trans (e.inv_hom_id_assoc s))))
        left_inv y := fiber_ext s (e.inv_hom_id_assoc y.left)
        right_inv y := fiber_ext s (e.hom_inv_id_assoc y.left) })
    (by
      intro P Q φ
      ext y
      exact fiber_ext s (Category.assoc e.hom y.left φ.hom.left).symm)

lemma fiberPrecompIso_hom_app_left (e : Spec (.of Ω) ≅ Spec (.of Ω)) (he : e.hom ≫ s = s)
    (P : Y.FiniteEtale) (y : (fiber s).obj P) :
    ((fiberPrecompIso s e he).hom.app P y).left = e.hom ≫ y.left :=
  rfl

variable (Y) in
/-- The geometric point `x̄ : Spec κ(x)‾ ⟶ Y` over a point `x` of `Y`, through the algebraic
closure of the residue field. -/
noncomputable abbrev residueFieldPoint (x : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField x))) ⟶ Y :=
  Y.algClosurePoint x

lemma residueFieldPoint_eq (x : Y) :
    residueFieldPoint Y x = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField x) (AlgebraicClosure (Y.residueField x)))) ≫
        Y.fromSpecResidueField x :=
  rfl

/-- The arithmetic Frobenius `σ_x : a ↦ a ^ #κ(x)` of the algebraic closure of a finite residue
field `κ(x)`, a `κ(x)`-algebra automorphism. -/
noncomputable def arithmeticFrobeniusAt (x : Y) [Finite (Y.residueField x)] :
    AlgebraicClosure (Y.residueField x) ≃ₐ[Y.residueField x]
      AlgebraicClosure (Y.residueField x) :=
  letI := Fintype.ofFinite (Y.residueField x)
  FiniteField.frobeniusAlgEquivOfAlgebraic (Y.residueField x) _

lemma arithmeticFrobeniusAt_apply (x : Y) [Finite (Y.residueField x)]
    (a : AlgebraicClosure (Y.residueField x)) :
    arithmeticFrobeniusAt x a = a ^ Nat.card (Y.residueField x) := by
  let := Fintype.ofFinite (Y.residueField x)
  rw [Nat.card_eq_fintype_card]
  rfl

/-- The automorphism `Spec σ` of `Spec Ω` induced by a ring automorphism `σ` of `Ω`. -/
noncomputable abbrev specMapIso {Ω' : Type u} [CommRing Ω'] (σ : Ω' ≃+* Ω') :
    Spec (.of Ω') ≅ Spec (.of Ω') :=
  Scheme.Spec.mapIso σ.toCommRingCatIso.op

/-- `Spec σ` of a `κ(x)`-algebra automorphism `σ` of `κ(x)‾` lies over `x̄`. -/
lemma specMapIso_hom_comp_residueFieldPoint (x : Y)
    (σ : AlgebraicClosure (Y.residueField x) ≃ₐ[Y.residueField x]
      AlgebraicClosure (Y.residueField x)) :
    (specMapIso σ.toRingEquiv).hom ≫ residueFieldPoint Y x = residueFieldPoint Y x := by
  rw [residueFieldPoint_eq, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact σ.commutes a

/-- **The geometric Frobenius at a point** `x` of `Y` with finite residue field: the
automorphism of the fibre functor at `x̄ : Spec κ(x)‾ ⟶ Y` given by precomposition with
`Spec σ_x⁻¹`, where `σ_x : a ↦ a ^ #κ(x)` is the arithmetic Frobenius of `κ(x)‾`. On the
geometric fibre `Hom_{k₀}(A, κ(x)‾)` of a constant cover `Y ×_{k₀} Spec A` it acts by
`β ↦ σ_x⁻¹ ∘ β`, the `[κ(x) : k₀]`-th power of the geometric Frobenius of `k₀`.
(blueprint `definition-weil-representation--1`) -/
noncomputable def geometricFrobeniusAt (x : Y) [Finite (Y.residueField x)] :
    fiber (residueFieldPoint Y x) ≅ fiber (residueFieldPoint Y x) :=
  fiberPrecompIso _ (specMapIso (arithmeticFrobeniusAt x).symm.toRingEquiv)
    (specMapIso_hom_comp_residueFieldPoint x _)

variable (G : Type*) [Group G] [∀ P : Y.FiniteEtale, MulAction G ((fiber s).obj P)]

/-- **Frobenius elements.** An element `g` of a fundamental group `G = π₁(Y, s)` is a Frobenius
element at a point `x` with finite residue field if, for some isomorphism `τ` of fibre functors
from the geometric point `x̄` over `x` to the base point `s` (a path from `x̄` to `s`), `g` acts
on the geometric fibres at `s` as the geometric Frobenius `F_x` at `x`, transported along `τ`:
`g • τ y = τ (F_x y)`. The Frobenius elements at `x` form a single conjugacy class of `G`,
since the paths from `x̄` to `s` form a torsor under `G`. (blueprint
`definition-weil-representation--1`) -/
def IsFrobeniusElement (x : Y) [Finite (Y.residueField x)] (g : G) : Prop :=
  ∃ τ : fiber (residueFieldPoint Y x) ≅ fiber s, ∀ (P : Y.FiniteEtale)
    (y : (fiber (residueFieldPoint Y x)).obj P),
      g • τ.hom.app P y = τ.hom.app P ((geometricFrobeniusAt x).hom.app P y)

end Frobenius

end AlgebraicGeometry.Scheme.FiniteEtale
