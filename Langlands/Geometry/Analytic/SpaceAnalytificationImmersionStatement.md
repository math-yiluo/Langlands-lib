# Analytification of open and closed immersions of algebraic spaces

`SpaceAnalytificationImmersionStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field and `f : X' ⟶ X` a morphism of
separated algebraic spaces over `Spec K` that are locally of finite type. Let
`(Y', p')` and `(Y, p)` be analytifications of `X'` and `X` in the sense of
`IsAnalytification`. Let `F : Y' ⟶ Y` be a morphism compatible with `f` on
affine test points. Then:
1. if `f` is an open immersion, the underlying continuous map of `F` is an open
   embedding;
2. if `f` is a closed immersion, the underlying continuous map of `F` is a
   closed embedding.

This module states the proposition only; it supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- algebraic spaces `X'` and `X` over `Spec (CommRingCat.of K)` and a morphism
  `f : X' ⟶ X`, with `IsSeparated` and `LocallyOfFiniteTypeOverBase` for both
  spaces;
- objects `Y'` and `Y` of `LocalizedCategory.{u, u, u}`, families
  `p' : PointFamily K X' Y'` and `p : PointFamily K X Y`, and the hypotheses
  `IsAnalytification K X' Y' p'` and `IsAnalytification K X Y p`;
- a morphism `F : Y' ⟶ Y` with `p' A P x ≫ F = p A P (RingPoints.map f x)` for
  every commutative `K`-algebra `A` in universe `u`, every finite polynomial
  presentation `P` of `A` and every `A`-point `x` of `X'`.

The conclusion is the conjunction of
- `AlgebraicSpace.IsOpenImmersion (hom f) →
  IsOpenEmbedding (localizedSpaceFunctor.map F)`;
- `AlgebraicSpace.IsClosedImmersion (hom f) →
  IsClosedEmbedding (localizedSpaceFunctor.map F)`.

`AlgebraicSpace.IsOpenImmersion` and `AlgebraicSpace.IsClosedImmersion` are the
Library's notions for morphisms of presheaves, from `SchemeLocalGeometry` and
`Thickening`. Such a morphism is representable, and every pullback along a
morphism from a scheme is an open, respectively closed, immersion of schemes.
`hom f` is the underlying morphism of presheaves of `f`.
`localizedSpaceFunctor.map F` is the continuous map of underlying spaces.

The statement concerns underlying topological spaces only. The Library has no
notion of open or closed immersion in `LocalizedCategory`, so the statement does
not claim that `F` is an immersion of analytic spaces. It also does not claim
the converse implications. By `SpaceAnalytificationMorphismStatement`, `F` is
the unique morphism compatible with `f`. This statement does not depend on that
one; it takes `F` and its compatibility as hypotheses.

## Provenance

The first source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), describes the analytification of [CT] for
separated algebraic spaces locally of finite type as compatible with "open and
closed immersions", among other properties.

The second source is Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Theorem 2.2.3, printed pp.7–8 (rigid-analytic setting): analytification
  carries open/closed immersions to sheaf maps that are relatively representable
  by Zariski-open/closed immersions.
- Printed p.19, last paragraph of §4.1: the `k`-analytic quotient, when it
  exists, "is functorial in `X` in a manner that respects the formation of fiber
  products and Zariski-open and Zariski-closed immersions".

The affine scheme case is Berkovich, *Spectral Theory and Analytic Geometry
over Non-Archimedean Fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Proposition 3.4.6(8), printed p.65/PDF p.79, and Proposition 3.4.7(2), printed
p.66/PDF p.80: a morphism of finite type is an open, respectively closed,
immersion if and only if its analytification is. On underlying spaces, the
affine forward implications are the Library's
`AffineAnalytificationImmersionStatement`.

The formulation is derived. The sources speak of immersions of analytic spaces;
this statement keeps only the consequence for underlying spaces, that an open
or closed immersion of analytic spaces is an open or closed embedding. It uses
the `k`-analytic analytification of Conrad–Temkin §4, modelled by
`IsAnalytification`. Only nontrivially normed `K` is treated, as the Library's
affine analytifications require.

## Why the statement should be true

This is not a Lean proof. Both open and closed immersions are monomorphisms, so
`X' ×_X X'` is `X'` through the diagonal. Analytification preserves fibre
products (`SpaceAnalytificationFibreProductStatement`), so `Y' ×_Y Y'` is `Y'`
through the diagonal. Every pair of points with a common image lifts to a point
of a fibre product of analytic spaces. Hence the underlying map of `F` is
injective.

Open immersions. `f` is étale, so `F` is étale
(`SpaceAnalytificationEtaleStatement`). Étale morphisms of analytic spaces are
open maps. An injective continuous open map is an open embedding.

Closed immersions. Let `x : Spec A → X` be an étale test point. The pullback of
`f` along `x` is a closed immersion `Spec(A/I) → Spec A`. By the fibre product
statement, the analytification of `Spec(A/I)` is the fibre product
`Y' ×_Y Spec(A)ᵃⁿ`. Its projection to `Spec(A)ᵃⁿ` is a closed embedding by the
affine case. A set in `Y` is closed when its preimages under the étale maps
`p(x)` are closed, since these maps are open and jointly surjective. For a closed
set `C ⊆ Y'`, the preimage of `F(C)` in `Spec(A)ᵃⁿ` is the image under the
second projection of the preimage of `C` under the first projection. It is
therefore closed. So the underlying map of `F` is closed, continuous and
injective, hence a closed embedding.
