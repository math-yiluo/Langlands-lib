import Langlands.Representation.Geometric.WeylStatement
import Langlands.AllField.Group.GL.Padic
/-! Concrete GL specializations of the Weyl and Bruhat prerequisites of BZ77. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicParabolicBruhatTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe uF

/-- The actual inverse permutation matrices parametrize parabolic double
cosets for every nonarchimedean local field. -/
def PadicParabolicBruhatTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n),
      Function.Bijective (parabolicDoubleCoset F B C)

end Langlands.AllField.Geometric
