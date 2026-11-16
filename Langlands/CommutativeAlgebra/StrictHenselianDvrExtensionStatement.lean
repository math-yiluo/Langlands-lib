import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Henselian

/-! # Statement: a faithfully flat strictly Henselian extension of a DVR -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every domain DVR has a faithfully flat algebra which is a strictly
Henselian domain DVR in the same universe. This is the existential consequence
of Stacks Tags 04GP, 07QM, and 0AP3 needed for fpqc descent. -/
def StrictHenselianDvrExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : HenselianLocalRing A) (_ : IsSepClosed (IsLocalRing.ResidueField A))
      (_ : Algebra R A), Module.FaithfullyFlat R A

end Langlands.CommutativeAlgebra
