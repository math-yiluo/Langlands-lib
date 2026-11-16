# Statement: analytification of algebraic spaces detects open and closed immersions

`SpaceAnalytificationAnalyticImmersionStatement` compares algebraic and
analytic immersions for analytifications of algebraic spaces. Let `K` be a
complete ultrametric nontrivially normed field and `f : X' ⟶ X` a morphism of
separated algebraic spaces over `Spec K` that are locally of finite type. Let
`(Y', p')` and `(Y, p)` be analytifications of `X'` and `X` in the sense of
`IsAnalytification`. Let `F : Y' ⟶ Y` be a morphism compatible with `f` on
affine test points. Then:
1. `f` is an open immersion if and only if `F` is an open immersion;
2. if `f` is a closed immersion, then `F` is a closed immersion;
3. if `f` is quasi-compact and `F` is a closed immersion, then `f` is a closed
   immersion.

The analytic notions are the morphism properties `openImmersion` and
`closedImmersion` of `AnalyticImmersion`. This module states the proposition
only; it supplies no proof.

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
- `AlgebraicSpace.IsOpenImmersion (hom f) ↔ openImmersion F`;
- `AlgebraicSpace.IsClosedImmersion (hom f) → closedImmersion F`;
- `IsQuasiCompactMorphism f → closedImmersion F →
  AlgebraicSpace.IsClosedImmersion (hom f)`.

`AlgebraicSpace.IsOpenImmersion` and `AlgebraicSpace.IsClosedImmersion` are the
Library's notions for morphisms of presheaves, from `SchemeLocalGeometry` and
`Thickening`. Such a morphism is representable, and every pullback along a
morphism from a scheme is an open, respectively closed, immersion of schemes.
`hom f` is the underlying morphism of presheaves of `f`.
`IsQuasiCompactMorphism` is the Library's quasi-compactness of morphisms of
algebraic spaces, from `SpaceMorphismProperties`. The analytic notions are
those of `AnalyticImmersion`, summarized in the Markdown of
`AffineAnalytificationAnalyticImmersionStatement`.

The quasi-compactness hypothesis in item 3 cannot be dropped. Take a field `K`
with an element `ϖ` of norm less than `1`. Let `X'` be the disjoint union of
countably many copies of `Spec K` and `X` the affine line. Map the `n`-th copy
to the rational point `ϖ⁻ⁿ`. This is a monomorphism but not a closed immersion,
since its image is not Zariski closed. The image of the induced analytic map is
a closed discrete set of rational points, since `|ϖ⁻ⁿ| → ∞`. The map is a closed
immersion of analytic spaces.

This statement is stronger than the Library's
`SpaceAnalytificationImmersionStatement`, which concerns underlying spaces only.
Together with `openImmersion.isOpenEmbedding` from `AnalyticImmersion`, item 1
gives the open half of that statement. The closed half would need the fact that
closed immersions are closed embeddings, which `AnalyticImmersion` does not
prove. The two statements do not depend on each other.

## Provenance

The motivating source is Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), registered as `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Printed p.19, in the proof of Proposition 5.11(3), describes the analytification
of [CT] for separated algebraic spaces locally of finite type as compatible with
"open and closed immersions", among other properties.

The main source is Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`. The pages
below were read in the registered file.
- Theorem 2.3.1, printed p.11 (rigid-analytic setting). For a map `f` of
  analytifiable algebraic spaces, `f` has a property `P` if and only if `fᵃⁿ`
  has it, where `P` may be "open immersion", among others. "Likewise, if `f` is
  of finite type then we may take `P` to be: closed immersion", among others.
  The proof works étale-locally on the target to reduce to schemes.
- Printed p.19, last paragraph of §4.1. "The arguments in §2 carry over
  essentially verbatim" to the `k`-analytic quotient, which "is functorial in
  `X` in a manner that respects the formation of fiber products and Zariski-open
  and Zariski-closed immersions".

For schemes, the comparison is Berkovich, *Spectral theory and analytic
geometry over non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Proposition 3.4.6(8), printed p.65/PDF p.79, treats open immersions of schemes
of locally finite type. Proposition 3.4.7(2), printed p.66/PDF p.80, treats
closed immersions of morphisms of finite type.

The formulation is derived. Conrad–Temkin prove Theorem 2.3.1 for rigid
analytification. Its `k`-analytic analogue rests on their remark that the
arguments of §2 carry over, and on Berkovich's theorems for schemes. The
statement uses the `k`-analytic analytification of Conrad–Temkin §4, modelled by
`IsAnalytification`. "Finite type" is expressed as quasi-compactness, since `f`
is locally of finite type when `X'` and `X` are. Item 2 needs no
quasi-compactness hypothesis, because closed immersions are quasi-compact. Only
nontrivially normed `K` is treated, as the Library's affine analytifications
require.

## Why the statement should be true

This is not a Lean proof. The argument follows the proof of Conrad–Temkin,
Theorem 2.3.1, in the `k`-analytic setting.

Let `x : Spec A → X` be an étale test point, and let `f_A : X'_A → Spec A` be
the pullback of `f` along `x`. By `SpaceAnalytificationFibreProductStatement`,
the analytification of `X'_A` is the fibre product `Y' ×_Y Spec(A)ᵃⁿ`, and
`f_Aᵃⁿ` is the base change of `F` along `p(x)`. The maps `p(x)` are étale and
jointly surjective. Being an open or closed immersion is étale-local on the
target for algebraic spaces. For analytic spaces and closed immersions this is
the descent argument of Conrad–Temkin §4.2, printed p.21, based on their
Lemma 4.2.4. For open immersions of analytic spaces, the image of `F` is open,
because its preimages under the open maps `p(x)` are open. `F` is an isomorphism
onto that open domain because it is one étale-locally, by descent of morphisms
along étale covers. Hence `f` is an open (closed) immersion exactly when each
`f_A` is, and `F` is one exactly when each `f_Aᵃⁿ` is.

So it suffices to treat a target `Spec A`. If `f_A` is an open or closed
immersion, then `X'_A` is a scheme, and Berkovich 1990, Propositions 3.4.6(8)
and 3.4.7(2), apply. For the converses, assume `F` is an open immersion, or `F`
is a closed immersion and `f` is quasi-compact. Then `f_Aᵃⁿ` is a monomorphism
with finite fibres, so `f_A` is quasi-finite. It is also separated, because
`X'` is separated. A quasi-finite separated algebraic space over a scheme is a
scheme, so `X'_A` is a scheme. Berkovich's propositions then give that `f_A` is
an open, respectively closed, immersion. In the closed case, quasi-compactness
of `f` makes `f_A` of finite type, as Proposition 3.4.7 requires.
