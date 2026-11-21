import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # Positive torus points killed by a set of simple roots lie in the split component

For a standard parabolic family with maximal split torus `T` and a standard index `J`, a point
of the positive real torus `A_T` on which every simple root in `J` takes the value `1` is, in
`G(𝔸)`, the image of a point of the positive split component `𝔄_{P_J}`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- A point `t` of the positive real torus `A_T ⊆ T(𝔸)` with `β(t) = 1` for every simple root
`β ∈ J` has the same image in `G(𝔸)` as some point of the positive split component of the
standard parabolic `P_J` (`StandardParabolicFamily.positiveSplitComponent`). -/
def PositiveTorusSplitComponentStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (𝓕 : StandardParabolicFamily F G)
    (J : StandardIndex F G 𝓕.i 𝓕.ν) (t : AdelicGroupPoints F 𝓕.T.toGrp),
    t ∈ PositiveRealTorus.intrinsicSubgroup F 𝓕.T →
    (∀ β ∈ J.1, Lie.characterValue β t = 1) →
    ∃ a ∈ 𝓕.positiveSplitComponent J,
      map F (𝓕.P J) G (𝓕.p J) a = map F 𝓕.T.toGrp G 𝓕.i t

end Langlands.Global
