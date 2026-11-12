import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Geometric connectedness of geometrically integral morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.TranslationOfSmoothFamily

/-- A geometrically integral morphism is geometrically connected. -/
lemma geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIntegral f] : GeometricallyConnected f :=
  ⟨fun _ _ y _ fst snd h ↦
    have : IrreducibleSpace _ :=
      GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) y fst snd h
    inferInstance⟩

end Langlands.AbelianScheme.TranslationOfSmoothFamily
