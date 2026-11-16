# Existence of analytifications of separated algebraic spaces

`SpaceAnalytificationExistenceStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field and `X` a separated algebraic
space over `Spec K` that is locally of finite type. Then there are an object `Y`
of the Library's localized category of analytic spaces and a family `p` of maps
from the analytifications of affine test points of `X` to `Y` such that
`IsAnalytification K X Y p` holds. This module states the proposition only; it
supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- an algebraic space `X : AlgebraicSpace (Spec (CommRingCat.of K))` in the
  Library's sense;
- hypotheses `IsSeparated X` and `LocallyOfFiniteTypeOverBase X`.

`IsSeparated X` is the Library's separatedness: the diagonal of the presheaf of
`X` is a representable closed immersion. `LocallyOfFiniteTypeOverBase X` asks
for one étale surjective atlas by a scheme locally of finite type over `Spec K`.
The conclusion is
`∃ (Y : LocalizedCategory.{u, u, u} (K := K)) (p : PointFamily K X Y),
IsAnalytification K X Y p`. `PointFamily` and `IsAnalytification` are the
definitions of `Langlands.Geometry.Analytic.SpaceAnalytification`. The predicate
asks that `p` be natural in the test algebra, étale on étale points and jointly
surjective from étale points, and that it carry fibre squares of affine test
points to pullback squares.

## Provenance

The source is Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Printed p.19, last paragraph of §4.1: if an étale chart `R ⇉ U` of an
  algebraic space `X` has a `k`-analytic quotient `𝒳 = 𝒰/ℛ` of the analytified
  relation (Definition 4.1.1, printed p.18), then `𝒳` is independent of the
  chart and is called the analytification of `X` in the sense of `k`-analytic
  spaces.
- Theorem 4.2.2, printed p.20 (Theorem 1.2.2, printed p.2): an étale equivalence
  relation `ℛ ⇉ 𝒰` of `k`-analytic spaces with `ℛ → 𝒰 × 𝒰` a closed immersion has
  a separated quotient.
- Printed p.20, after Theorem 4.2.1: for an étale chart of a separated algebraic
  space, the analytified relation is an étale equivalence relation with
  `ℛ → 𝒰 × 𝒰` a closed immersion, by Berkovich's dictionary [Ber2, 3.3.11].
- Printed p.25, end of §4.3: from Theorem 4.2.2, `X` admits an analytification
  in the sense of `k`-analytic spaces, and it is separated, good and strictly
  `k`-analytic.

The second source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), uses this analytification for separated
algebraic spaces locally of finite type over `k`.

The formulation is derived. The analytic quotient of Definition 4.1.1 is
expressed by `IsAnalytification`, as explained in that definition's Markdown.
The analytic spaces are objects of the Library's localized category of
saturated atlas presentations. Only nontrivially normed `K` is treated, as the
Library's affine analytifications require.

## Why the statement should be true

Choose an étale atlas of `X` by affine schemes `Spec Aᵢ` of finite type over
`K`. Because `X` is separated, every `Spec Aᵢ ×_X Spec Aⱼ` is a closed subscheme
of `Spec Aᵢ ×_K Spec Aⱼ`, hence affine. Theorem 4.2.2 gives the quotient `Y` of
the analytified relation. For an arbitrary test point `x : Spec A → X`, the
map `Spec(A)ᵃⁿ → Y` is the analytification of `x` (Conrad–Temkin, Theorem 2.2.3
and the `k`-analytic version on p.19). It is natural in `A`, and it is étale
when `x` is étale (Theorem 2.3.1, printed p.11). The atlas maps are jointly
surjective. Compatibility with fibre products (Theorem 2.2.3 and its
`k`-analytic version) gives the pullback condition. The proof must also show
that Berkovich's analytic spaces and these properties are realized in the
Library's localized category.
