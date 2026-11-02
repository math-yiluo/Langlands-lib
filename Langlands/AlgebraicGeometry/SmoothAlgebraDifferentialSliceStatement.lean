import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Etale.Basic

/-! # An algebraic differential slicing criterion -/

universe u v w t

namespace Langlands.AlgebraicGeometry

open Algebra TensorProduct

/-- A finite set of equations in a smooth algebra cuts out an etale algebra
when its differentials form a basis along the quotient. -/
def SmoothAlgebraDifferentialSliceStatement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{w} R S) [Algebra.Smooth R P.Ring]
    (ι : Type t) [Finite ι] (f : ι → P.Ring)
    (hf : Ideal.span (Set.range f) = P.ker)
    (b : Module.Basis ι S P.CotangentSpace),
    (∀ i, b i = 1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (f i)) →
      Algebra.Etale R S

end Langlands.AlgebraicGeometry
