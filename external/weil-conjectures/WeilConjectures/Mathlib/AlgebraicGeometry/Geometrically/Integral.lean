/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometrically integral morphisms

An irreducible space is connected, so a geometrically irreducible morphism, and in particular a
geometrically integral one, is geometrically connected.

A flat morphism with geometrically reduced (resp. integral) fibres followed by a morphism locally
of finite type with geometrically reduced (resp. integral) fibres has geometrically reduced
(resp. integral) fibres. In particular a product of two geometrically integral schemes of finite
type over a field is geometrically integral.

## Main statements

- `AlgebraicGeometry.GeometricallyIntegral.geometricallyConnected`
- `AlgebraicGeometry.GeometricallyReduced.comp_of_flat`
- `AlgebraicGeometry.GeometricallyIntegral.comp_of_flat`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section GeometricallyConnected

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A geometrically irreducible morphism is geometrically connected: every geometric fibre is
irreducible, hence connected. -/
lemma GeometricallyIrreducible.geometricallyConnected [GeometricallyIrreducible f] :
    GeometricallyConnected f :=
  ⟨fun _ _ y _ fst snd h ↦
    haveI := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) y fst snd h
    inferInstance⟩

/-- A geometrically integral morphism is geometrically connected. -/
lemma GeometricallyIntegral.geometricallyConnected [GeometricallyIntegral f] :
    GeometricallyConnected f :=
  GeometricallyIrreducible.geometricallyConnected f

end GeometricallyConnected

section Comp

variable {X Y Z : Scheme.{u}}

/-- A flat morphism with geometrically reduced fibres followed by a morphism locally of finite
type with geometrically reduced fibres has geometrically reduced fibres: over a field `K`, the
scheme `X ×_Z Spec K` is flat over the reduced and locally noetherian scheme `Y ×_Z Spec K`,
with geometrically reduced fibres. -/
theorem GeometricallyReduced.comp_of_flat (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyReduced f]
    [GeometricallyReduced g] [Flat f] [LocallyOfFiniteType g] :
    GeometricallyReduced (f ≫ g) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have : IsReduced (pullback g y) :=
    pullback_of_geometrically (GeometricallyReduced.geometrically_isReduced (f := g)) K y
  exact isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso g y f).inv

/-- A flat and universally open morphism with geometrically integral fibres followed by a
universally open morphism locally of finite type with geometrically integral fibres has
geometrically integral fibres. -/
theorem GeometricallyIntegral.comp_of_flat (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIntegral f]
    [GeometricallyIntegral g] [Flat f] [UniversallyOpen f] [UniversallyOpen g]
    [LocallyOfFiniteType g] : GeometricallyIntegral (f ≫ g) := by
  have := GeometricallyReduced.comp_of_flat f g
  have := GeometricallyIrreducible.comp f g
  exact .of_geometricallyReduced_of_geometricallyIrreducible _

end Comp

end AlgebraicGeometry
