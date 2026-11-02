import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.Multiplication

/-! # Statement: endomorphisms of the multiplicative group over an integral domain -/

open AlgebraicGeometry

namespace Langlands.GroupScheme.Gm

universe u

/-- Over the spectrum of an integral domain `R`, integer multiplication `n ↦ [n]` is a bijection
from `ℤ` onto the group-scheme endomorphisms of `𝔾_{m, Spec R}`. -/
def EndomorphismsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsDomain R],
    Function.Bijective (multiplication (Gm (Spec R)).toGrp)

end Langlands.GroupScheme.Gm
