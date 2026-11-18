import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-!
# Nilpotent elements and degenerate cosets (KP Definition 13.6.5)

An element `X` of `𝔤 = Lie(G)` is nilpotent in KP's sense if some 1-parameter subgroup
`ν : 𝔾_m → G` defined over `k` satisfies `lim_{t → 0} Ad(ν(t)) X = 0`, that is, if `X` lies in
the sum of the weight spaces of `Ad ∘ ν` with positive weight. A linear form `X ∈ 𝔤*` is
nilpotent if `lim_{t → 0} ν(t) · X = 0` for the coadjoint action, that is, if `X` vanishes on the
weight spaces of `Ad ∘ ν` with weight `≥ 0`. A coset `X + M` is degenerate if it contains a
nilpotent element.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- For a 1-parameter subgroup `ν : 𝔾_m → G`, the sum `𝔤_{>0}(ν)` of the weight spaces of
`Ad ∘ ν` in `Lie(G)` with positive weight: the published `RelativeRoot.positiveWeightSpan` for
`ν` and the identity character `t ↦ t` of `𝔾_m`, i.e. the sum over the characters `t ↦ tⁿ`,
`n > 0`. -/
def cocharacterPositiveLie (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Submodule k (Additive (lieKernel G k)) :=
  RelativeRoot.positiveWeightSpan ν (𝟙 _)

/-- For a 1-parameter subgroup `ν : 𝔾_m → G`, the sum `𝔤_{≥0}(ν)` of the weight spaces of
`Ad ∘ ν` in `Lie(G)` with weight `≥ 0`: the published `nonnegativeWeightSpan` for `ν` and the
identity cocharacter of `𝔾_m`, i.e. the sum over the characters `χ` of `𝔾_m` with
`⟨χ, id⟩ ≥ 0`. -/
def cocharacterNonnegativeLie (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Submodule k (Additive (lieKernel G k)) :=
  nonnegativeWeightSpan ν (𝟙 _)

variable {R : Type u} [CommRing R] [Algebra R k]

/-- KP Definition 13.6.5 for `𝔤`: `X` is nilpotent if some 1-parameter subgroup
`ν : 𝔾_m → G` over `k` contracts it, `lim_{t → 0} Ad(ν(t)) X = 0`, i.e. `X ∈ 𝔤_{>0}(ν)`.
The ring `R` only selects the type synonym `GenericLie R G` of `Lie(G)`. -/
def IsCocharacterNilpotent (X : GenericLie R G) : Prop :=
  ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
    GenericLie.equiv R G X ∈ cocharacterPositiveLie ν

/-- KP Definition 13.6.5 for `𝔤*`: a `k`-linear form `X` on `Lie(G)` is nilpotent if some
1-parameter subgroup `ν : 𝔾_m → G` over `k` contracts it under the coadjoint action. Since
`(ν(t) · X)(Y) = t^{-n} X(Y)` for `Y` of weight `n`, this says that `X` vanishes on
`𝔤_{≥0}(ν)`. -/
def IsCocharacterNilpotentDual (X : Module.Dual k (GenericLie R G)) : Prop :=
  ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
    ∀ Y : GenericLie R G, GenericLie.equiv R G Y ∈ cocharacterNonnegativeLie ν → X Y = 0

/-- KP Definition 13.6.5: the coset `X + M` of an `R`-submodule `M` of `𝔤` is degenerate if it
contains a nilpotent element. KP use `M = 𝔤_{x,r+}` and `X ∈ 𝔤_{x,r}`. -/
def IsDegenerateLieCoset (M : Submodule R (GenericLie R G)) (X : GenericLie R G) : Prop :=
  ∃ Y : GenericLie R G, IsCocharacterNilpotent Y ∧ Y - X ∈ M

/-- KP Definition 13.6.5: the coset `X + M` of an `R`-submodule `M` of `𝔤*` is degenerate if
it contains a nilpotent element. KP use `M = 𝔤*_{x,r+}` and `X ∈ 𝔤*_{x,r}`. -/
def IsDegenerateDualCoset (M : Submodule R (Module.Dual k (GenericLie R G)))
    (X : Module.Dual k (GenericLie R G)) : Prop :=
  ∃ Y : Module.Dual k (GenericLie R G), IsCocharacterNilpotentDual Y ∧ Y - X ∈ M

end Langlands.Geometry.Building
