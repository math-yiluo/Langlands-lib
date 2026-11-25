/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The explicit restriction-adjunction lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: def-weil-pbc-flat-base-change-restricted-lift).
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

-- The nested restriction-adjunction functors require additional elaboration fuel.
/-- Restrict a fixed lift by the restriction adjunction, after transporting the
pushforward square through its canonical composition and congruence isomorphisms.
Conjugate by the two specified restricted resolution comparisons. This is an
explicit construction; no existence theorem or unproved choice supplies data.
Source: Stacks, Tags 01FB and 01E4.
(blueprint: def-weil-pbc-flat-base-change-restricted-lift) -/
def flatBaseChangeRestrictedLift {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) :
    D.source.resolution.cocomplex ⟶
      ((pushforward ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
        ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.resolution.cocomplex := by
  let U := f ⁻¹ᵁ V
  let W := (pullback.snd g f) ⁻¹ᵁ U
  have : (restrictFunctor U.ι).Additive :=
    (restrictAdjunction U.ι).left_adjoint_additive
  let h := (pullback.snd g f).resLE U W le_rfl
  let B := D.target.resolution.cocomplex
  let P := (pushforward U.ι).mapHomologicalComplex (ComplexShape.up ℕ)
  let H := (pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)
  let G := (pushforward (pullback.snd g f)).mapHomologicalComplex (ComplexShape.up ℕ)
  let e₁ := NatIso.mapHomologicalComplex (pushforwardComp W.ι (pullback.snd g f))
    (ComplexShape.up ℕ)
  let e₂ := NatIso.mapHomologicalComplex
    (pushforwardCongr ((pullback.snd g f).resLE_comp_ι (U := U) (V := W) le_rfl))
    (ComplexShape.up ℕ)
  let e₃ := NatIso.mapHomologicalComplex (pushforwardComp h U.ι) (ComplexShape.up ℕ)
  let w := ((restrictAdjunction W.ι).unit.mapHomologicalComplex
    (ComplexShape.up ℕ)).app J.cocomplex
  let b : I.cocomplex ⟶ P.obj (H.obj B) :=
    t ≫ G.map w ≫ e₁.hom.app (((restrictFunctor W.ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      e₂.inv.app (((restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      e₃.inv.app (((restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) ≫
      P.map (H.map D.target.comparison.inv)
  exact D.source.comparison.hom ≫
    (((restrictAdjunction U.ι).mapHomologicalComplex (ComplexShape.up ℕ)).homEquiv
      I.cocomplex (H.obj B)).symm b

end AlgebraicGeometry.Scheme.Modules
