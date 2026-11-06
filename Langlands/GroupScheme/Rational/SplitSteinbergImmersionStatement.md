# Closed immersion of the supplied split Steinberg product

`Langlands.GroupScheme.SplitSteinbergImmersionStatement.{u}` is a Prop-valued
target. This file defines the proposition and does not prove it.

## Hypotheses

The proposition quantifies over the following data.

- An arbitrary field `k : Type u`, in any universe `u`. The characteristic is
  arbitrary, and finite and imperfect fields are allowed. No algebraic closure,
  perfectness or infinitude hypothesis appears.
- An actual group scheme `G : GroupScheme (Spec (CommRingCat.of k))` with
  `[IsAffineHom G.X.hom]`.
- A supplied `p : SplitPinning G`. This structure records that `G` is connected
  reductive (`IsConnectedReductive G`). It also records an actual split maximal
  torus `p.inclusion : p.torus.toGrp ⟶ G` and a finite reduced root datum
  `p.rootDatum`, whose roots are the roots of `G` relative to that torus by
  `IsRootDatumOf`. Finally it records a base `p.base` and Lie trivializations
  `p.pinning` on the simple-root weight spaces.
- The premise `IsSemisimple G`, which requires connected reductivity and a
  finite scheme-theoretic centre. It matches the semisimple setting of
  Steinberg §7. No simple-connectedness premise is added.
- A natural number `r` and an ordering `e : Fin r ≃ p.base.support` of the
  simple roots. Every ordering is included. If `r` differs from the number of
  simple roots then no such `e` exists.
- A supplied family `x : p.NormalizedSimpleRootParametrizations`. For each
  simple root `a`, `x a` is a group-scheme homomorphism from the standard
  additive group. It represents the whole intrinsic root subgroup functor
  `RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)` on every test scheme,
  and it is a closed subgroup inclusion. Its torus-equivariance and
  Lie-derivative normalization fields are as published.
- A supplied family `n : p.SimpleReflectionRepresentatives`. For each simple
  root `a`, `n a` is a rational point of `G` with an actual torus automorphism.
  The point normalizes the torus through that automorphism, whose character
  action `characterAut` is `p.rootDatum.reflection a`. In the Library's
  convention `characterAut` precomposes characters with the inverse torus
  automorphism. Every such family is included; no preferred representative is
  chosen.

None of these data is asserted to exist. All types and conventions are those
of the published module `Langlands.GroupScheme.Rational.SteinbergRootProduct`,
unchanged.

## Conclusion

The conclusion is

```lean
IsClosedImmersion (SplitPinning.steinbergProduct e x n).left
```

Here `SplitPinning.steinbergProduct e x n` is the published morphism over
`Spec k` from `(VectorGroup.groupScheme (CommRingCat.of k) r).X` to `G.X`. Its
source is standard affine `r`-space, the spectrum of the polynomial ring in
`Fin r` variables. On every test scheme `T` and coordinates `c : Fin r → Γ(T, ⊤)`
it is the ordered product

`x_(e 0)(c 0) · n_(e 0) · x_(e 1)(c 1) · n_(e 1) ⋯ x_(e (r-1))(c (r-1)) · n_(e (r-1))`

in increasing `Fin r` order, as stated by `comp_steinbergProduct`. The
proposition asserts that the underlying morphism of schemes (`.left`) into the
original `G` is a closed immersion. For `r = 0` the source is affine `0`-space
over `k`, and the published lemma `steinbergProduct_zero` identifies the map
with the constant identity morphism.

## Source and derived translation

R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publ. Math.
IHÉS 25 (1965), registered as `steinberg-1965-regular-elements-semisimple-groups`,
SHA-256 `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`.
The relevant passages are the following.

- Theorem 1.4, printed p.50 (PDF p.3), defines `N = X_1σ_1 ⋯ X_rσ_r`. Here
  `X_i` is the root subgroup of the simple root `a_i` and `σ_i` is a normalizer
  element representing the reflection of `a_i`.
- 2.2 b), printed p.52 (PDF p.5), states that the product map from the positive
  root subgroups, in any fixed order, to `U` is an isomorphism of varieties.
- Theorem 7.1, Lemmas 7.2–7.3 and the proof of 7.1, printed pp.66–67
  (PDF pp.19–20).

Theorem 7.1 states that `N` is closed and irreducible in `G` and that
`(c_i) ↦ ∏ x_i(c_i)σ_i` is an isomorphism of varieties from affine `r`-space
onto `N`. Lemma 7.2 sets `β_i = w_1 ⋯ w_(i-1) a_i` and `w = w_1 ⋯ w_r`. It shows
that the `β_i` are positive, distinct and independent, and that they are
exactly the positive roots made negative by `w⁻¹`. It also shows that no sum of
two of them is a root. Lemma 7.3 shows that the product `X_w = ∏ X_(β_i)` is
direct and that `N = X_w σ_w`. The proof of 7.1 combines this with 2.2 b).
Steinberg works over an algebraically closed field with a semisimple group
that need not be simply connected. The pages were read from the registered
original and the file was rehashed. No source-specific errata note was found.

The Lean proposition is a derived, internal scheme-theoretic translation of the
closedness and isomorphism assertions of Theorem 7.1. Theorem 7.1 says that the ordered parametrization is
an isomorphism of affine `r`-space onto the closed subvariety `N`. Here this
becomes the statement that the actual scheme morphism is a closed immersion,
that is, an isomorphism onto a closed subscheme. The irreducibility of `N` and
the uniqueness of components are not stated separately.

The expected argument is Steinberg's. To match his indexing, write
`a_i = e (i-1)`, `x_i = x a_i` and `σ_i = n a_i` for `1 ≤ i ≤ r`, and put
`τ_i = σ_1 ⋯ σ_(i-1)`. Then the product equals
`(∏_i τ_i x_i(c_i) τ_i⁻¹) · σ_1 ⋯ σ_r`, and the `i`-th factor parametrizes the
root subgroup of `β_i`. The map `c ↦ ∏_i τ_i x_i(c_i) τ_i⁻¹` is then a closed
immersion by 7.2–7.3 and 2.2 b). Right translation by the rational point
`σ_1 ⋯ σ_r` is an automorphism of the scheme `G`. This outline does not use the
finite-centre part of `IsSemisimple G`; the premise is retained to match
Steinberg's setting.

## Proof obligations retained

The statement does not discharge the following comparisons. They belong to its
proof, which is a separate successor task.

- **Arbitrary fields and schemes.** Steinberg's theorem concerns varieties over
  an algebraically closed field. The target is a closed immersion of schemes
  over any field `k`. A proof must either establish the split structure
  directly over `k` or pass to an algebraic closure and descend the closed
  immersion property. The descent route also needs compatibility of the root
  maps, the representatives and the intrinsic root functors with base change.
- **Intrinsic root functors.** Each `x a` represents the Library's intrinsic
  functor `RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)`, defined by
  orbit extensions on every test scheme. A proof must identify it with
  Steinberg's root subgroup `X_a`.
- **Conjugated root subgroups.** A proof must show that conjugation by the
  supplied representatives carries these functors to the root subgroups of the
  roots `β_i`. This includes matching the `characterAut` convention with
  Steinberg's action of `W` on roots.
- **Positive roots.** A proof must show that the product of the positive root
  subgroups for the roots `β_i` is an actual closed subscheme isomorphic to the
  product of the factors. This is the scheme-theoretic form of 2.2 b) and 7.3.

## Scope

The target asserts no existence of the pinning, root maps or representatives.
It asserts no regularity of the elements of `N` and no comparison with an
invariant quotient or the fundamental characters (Steinberg 7.9). It asserts no
quasi-split descent and no rational lifting. Quasi-split groups are not
inferred to be split: the `SplitPinning` is supplied. The parent
`QuasiSplitSteinbergQuotientStatement` pair, the pairs it imports and the
`SteinbergRootProduct` pair are unchanged.

The Lean statement was first drafted by Worker 1490 and is used here unchanged
apart from its docstring.
