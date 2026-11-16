# Morphisms of analytifications of algebraic spaces

`SpaceAnalytificationMorphismStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field, and let `f : X' ⟶ X` be a
morphism of algebraic spaces over `Spec K`, with `X'` separated and locally of
finite type. Let `(Y', p')` be an analytification of `X'` and `(Y, p)` one of
`X`, in the sense of `IsAnalytification`. Then there is exactly one morphism
`F : Y' ⟶ Y` in the Library's localized category such that
`p' A P x ≫ F = p A P (RingPoints.map f x)` for every commutative `K`-algebra `A`
in universe `u`, every finite polynomial presentation `P` of `A` and every
`A`-point `x` of `X'`. This module states the proposition only; it supplies no
proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- algebraic spaces `X'` and `X` over `Spec (CommRingCat.of K)` and a morphism
  `f : X' ⟶ X`;
- hypotheses `IsSeparated X'` and `LocallyOfFiniteTypeOverBase X'`;
- objects `Y'` and `Y` of `LocalizedCategory.{u, u, u}`, families
  `p' : PointFamily K X' Y'` and `p : PointFamily K X Y`, and hypotheses
  `IsAnalytification K X' Y' p'` and `IsAnalytification K X Y p`.

The conclusion is `∃! F : Y' ⟶ Y, ∀ A P x, p' A P x ≫ F = p A P (RingPoints.map f x)`.
`RingPoints.map f x` is the composite of the point `x` with `f`. No hypothesis
is placed on `X` beyond having the analytification `(Y, p)`.

Taking `X' = X`, `f = 𝟙 X` and two analytifications of `X` gives morphisms in
both directions whose composites are identities by uniqueness. So an
analytification is unique up to unique isomorphism compatible with the maps
from test points. That consequence is not stated separately here.

## Provenance

The source is Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Theorem 2.2.3, printed pp.7–8 (rigid-analytic setting): for `f : X' → X` and
  étale charts with a lift `F : U' → U`, the map `fᵃⁿ` induced by `Fᵃⁿ` depends
  only on `f`, and `X ↦ Xᵃⁿ` is a functor.
- Printed p.19, last paragraph of §4.1: the arguments of §2 carry over to
  `k`-analytic quotients, which are independent of the chart and functorial in
  `X`.
- Printed p.19, paragraph after Example 4.1.3: a quotient in the sense of
  Definition 4.1.1 represents the quotient sheaf `𝒰/ℛ` on the étale site of
  `k`-analytic spaces. The basis is Theorem 4.1.2 and [Ber2, 4.1.5]
  (representable functors are étale sheaves).

The second source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), uses "a functorial theory of analytification".

The formulation is derived. Morphisms are characterized by their composites with
the maps from test points, not by charts and lifts.

## Why the statement should be true

Choose an étale atlas of `X'` by affine schemes `Spec Aᵢ`. Separatedness makes
`Spec Aᵢ ×_{X'} Spec Aⱼ = Spec Cᵢⱼ` affine. By `IsAnalytification` the maps
`Spec(Aᵢ)ᵃⁿ → Y'` form an étale covering of `Y'`, and their fibre products over
`Y'` are the `Spec(Cᵢⱼ)ᵃⁿ`. The maps `p(f ∘ xᵢ)` agree on these overlaps by
naturality of `p`. Representable functors are étale sheaves, so they descend to
a unique `F : Y' → Y`. For an arbitrary test point `x : Spec A → X'`, the affine
schemes `Spec A ×_{X'} Spec Aᵢ` give an étale covering of `Spec(A)ᵃⁿ`. On this
covering both `p' A P x ≫ F` and `p A P (f ∘ x)` restrict to the same maps, so
they are equal. The proof must also realize these facts in the Library's
localized category.
