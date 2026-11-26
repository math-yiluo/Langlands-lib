import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian

/-! # Statement: an unramified strictly Henselian extension of a DVR -/

universe u

open IsLocalRing

namespace Langlands.CommutativeAlgebra

/-- Every discrete valuation ring `V` has a local homomorphism `V → W` to a strictly
Henselian discrete valuation ring `W` in the same universe such that the maximal ideal
of `V` generates the maximal ideal of `W` and the residue field of `W` is a separable
algebraic extension of the residue field of `V`. A strict henselization of `V` is such
an extension (Stacks Tags 04GP and 0AP3). -/
def UnramifiedStrictHenselianDvrExtensionStatement : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : HenselianLocalRing W) (_ : IsSepClosed (ResidueField W)) (_ : Algebra V W)
      (_ : IsLocalHom (algebraMap V W)),
      (maximalIdeal V).map (algebraMap V W) = maximalIdeal W ∧
        Algebra.IsSeparable (ResidueField V) (ResidueField W)

end Langlands.CommutativeAlgebra
