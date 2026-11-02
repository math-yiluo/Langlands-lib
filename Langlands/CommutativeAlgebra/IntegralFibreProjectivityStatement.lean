import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-! # Projectivity for flat algebras with geometrically integral fibres -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Stacks 05FT: a flat finitely presented algebra with geometrically integral
fibres is projective as a module over its base. -/
def IntegralFibreProjectivityStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    Algebra.FinitePresentation R S →
    Module.Flat R S →
    AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))) →
    Module.Projective R S

end Langlands.CommutativeAlgebra
