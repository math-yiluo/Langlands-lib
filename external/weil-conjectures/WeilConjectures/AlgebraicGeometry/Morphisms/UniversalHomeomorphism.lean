/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Universal homeomorphisms of schemes

A morphism of schemes is a *universal homeomorphism* if every base change of it is a
homeomorphism on underlying topological spaces. By [Stacks 04DF] this holds if and only if
the morphism is integral, universally injective and surjective, and this is the definition
we take: all three are readily available as classes, while quantifying over all base
changes is not.

## Main definitions

- `AlgebraicGeometry.IsUniversalHomeomorphism`: the class of universal homeomorphisms.
- `AlgebraicGeometry.IsUniversalHomeomorphism.homeomorph`: the homeomorphism of underlying
  topological spaces induced by a universal homeomorphism.

## Main statements

- `AlgebraicGeometry.isUniversalHomeomorphism_eq`: the `MorphismProperty` description of
  the class as the infimum of being integral, universally injective and surjective.
- `AlgebraicGeometry.Scheme.Hom.isHomeomorph`: a universal homeomorphism is in particular a
  homeomorphism on underlying spaces.
- `AlgebraicGeometry.IsUniversalHomeomorphism.of_comp`: if `g ≫ f` and `f` are universal
  homeomorphisms, then so is `g`.
- `AlgebraicGeometry.isUniversalHomeomorphism_le_universally_isHomeomorph`: a universal
  homeomorphism stays a homeomorphism after an arbitrary base change. This is the direction
  of [Stacks 04DF] that the definition does not make trivial; the converse, that a morphism
  all of whose base changes are homeomorphisms is integral, is not formalised here.

## Implementation notes

The stability properties (composition, base change, isomorphisms) are all proved by
rewriting along `AlgebraicGeometry.isUniversalHomeomorphism_eq` and appealing to the
corresponding properties of the three defining classes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-- A morphism of schemes is a universal homeomorphism if it is integral, universally
injective and surjective; equivalently, if every base change of it is a homeomorphism
on underlying spaces. -/
@[mk_iff, stacks 04DF]
class IsUniversalHomeomorphism (f : X ⟶ Y) : Prop
    extends IsIntegralHom f, UniversallyInjective f, Surjective f

/-- As a `MorphismProperty`, being a universal homeomorphism is the infimum of being
integral, universally injective and surjective. -/
theorem isUniversalHomeomorphism_eq :
    @IsUniversalHomeomorphism = (@IsIntegralHom ⊓ @UniversallyInjective ⊓ @Surjective :
      MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [isUniversalHomeomorphism_iff]
  exact and_assoc.symm

/-- A universal homeomorphism is a homeomorphism on underlying topological spaces. -/
theorem Scheme.Hom.isHomeomorph (f : X ⟶ Y) [IsUniversalHomeomorphism f] :
    IsHomeomorph f.base :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f.continuous, f.isClosedMap, f.injective, f.surjective⟩

namespace IsUniversalHomeomorphism

instance : IsStableUnderComposition @IsUniversalHomeomorphism.{u} :=
  isUniversalHomeomorphism_eq ▸ inferInstance

instance : IsStableUnderBaseChange @IsUniversalHomeomorphism.{u} :=
  isUniversalHomeomorphism_eq ▸ inferInstance

/-- An isomorphism is a universal homeomorphism. This is subsumed by the instance for
surjective closed immersions below, but is kept as a short cut for the instance search
behind `IsMultiplicative.id_mem`. -/
instance (f : X ⟶ Y) [IsIso f] : IsUniversalHomeomorphism f where

instance : IsMultiplicative @IsUniversalHomeomorphism.{u} where
  id_mem _ := inferInstance

instance comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsUniversalHomeomorphism f]
    [IsUniversalHomeomorphism g] : IsUniversalHomeomorphism (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

instance (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism g] :
    IsUniversalHomeomorphism (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism f] :
    IsUniversalHomeomorphism (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

/-- A surjective closed immersion is a universal homeomorphism. In particular a nilpotent
thickening is a universal homeomorphism, which is the case of [Stacks 03SI] usually quoted
as invariance of the étale site under nilpotent thickenings. -/
instance (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f] : IsUniversalHomeomorphism f where

/-- **Cancellation**: if `g ≫ f` and `f` are universal homeomorphisms, then so is `g`.
The morphism `f` is separated since it is injective, so `g` is integral; `g` is surjective
since `g ≫ f` is surjective and `f` is injective; and `g` is injective on field-valued points
since `g ≫ f` is. -/
theorem of_comp (g : X ⟶ Y) (f : Y ⟶ Z) [IsUniversalHomeomorphism (g ≫ f)]
    [IsUniversalHomeomorphism f] : IsUniversalHomeomorphism g := by
  have : IsSeparated f := isSeparated_of_injective f f.injective
  have : IsIntegralHom g := .of_comp g f
  have : Surjective g := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := (g ≫ f).surjective (f y)
    exact ⟨x, f.injective (by rwa [← Scheme.Hom.comp_apply])⟩
  have : UniversallyInjective g := by
    have hgf := (tfae_universallyInjective (g ≫ f)).out 1 2
    have hg := (tfae_universallyInjective g).out 1 2
    rw [hg]
    intro K _ g₁ g₂ h
    exact hgf.mp inferInstance K (by simpa using congr($h ≫ f))
  exact { }

/-- The homeomorphism of underlying topological spaces induced by a universal
homeomorphism.

This is not called `Scheme.Hom.homeomorph`, since that name is taken by the homeomorphism
attached to an isomorphism of schemes. -/
noncomputable def homeomorph (f : X ⟶ Y) [IsUniversalHomeomorphism f] : X ≃ₜ Y :=
  f.isHomeomorph.homeomorph

end IsUniversalHomeomorphism

/-- **A universal homeomorphism stays a homeomorphism after an arbitrary base change**: this
is the nontrivial direction of [Stacks 04DF] for the definition of
`AlgebraicGeometry.IsUniversalHomeomorphism` used here. -/
@[stacks 04DF]
theorem isUniversalHomeomorphism_le_universally_isHomeomorph :
    @IsUniversalHomeomorphism.{u} ≤
      (topologically @IsHomeomorph : MorphismProperty Scheme.{u}).universally := by
  rw [← IsStableUnderBaseChange.universally_eq (P := @IsUniversalHomeomorphism.{u})]
  refine universally_mono ?_
  intro X Y f hf
  exact f.isHomeomorph

end AlgebraicGeometry
