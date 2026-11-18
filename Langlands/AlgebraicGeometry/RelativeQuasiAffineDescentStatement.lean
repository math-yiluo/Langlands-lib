import Langlands.AlgebraicGeometry.RelativeQuasiAffine
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Statements: descent of quasi-affine morphisms -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- **Quasi-affineness descends along flat, quasi-compact, surjective base change**
(Stacks Project, Descent, Lemma 35.23.22, Tag 02L7, for the fpqc covering `{p : S' ⟶ S}`).
Let `f : X ⟶ S` be a morphism of schemes and let `p : S' ⟶ S` be flat, quasi-compact
and surjective. If the base change `X ×_S S' ⟶ S'` of `f` along `p` is quasi-affine,
then `f` is quasi-affine. All schemes lie in one arbitrary universe and no further
hypothesis is imposed on `X`, `S` or `S'`. -/
def RelativeQuasiAffineFlatDescentStatement : Prop :=
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (p : S' ⟶ S) [Flat p] [QuasiCompact p] [Surjective p],
    IsQuasiAffineOver (pullback.snd f p) → IsQuasiAffineOver f

/-- **Quasi-affineness descends along étale covers**
(Stacks Project, Descent, Lemma 35.23.22, Tag 02L7, for an étale covering).
Let `f : X ⟶ S` be a morphism of schemes and let `𝒰` be a jointly surjective family of
étale morphisms `𝒰.f i : 𝒰.X i ⟶ S`, indexed by an arbitrary, possibly infinite, type
`𝒰.I₀` in an independent universe. If every base change `X ×_S 𝒰.X i ⟶ 𝒰.X i` of `f` is
quasi-affine, then `f` is quasi-affine. -/
def RelativeQuasiAffineEtaleDescentStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : Scheme.Cover.{v} (Scheme.precoverage @Etale) S),
    (∀ i : 𝒰.I₀, IsQuasiAffineOver (pullback.snd f (𝒰.f i))) → IsQuasiAffineOver f

end Langlands.AlgebraicGeometry
