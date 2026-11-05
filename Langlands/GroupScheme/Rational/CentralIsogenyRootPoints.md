# Rational relative root points under a central isogeny

This is a derived prerequisite for comparing an apartment with an apartment of
a simply connected cover. It uses the existing full-torus orbit definition of
`RelativeRoot.subgroup`, central-isogeny contracting-point transport, fpqc
descent, proper affine-line extension and uniqueness of separated orbit limits.
The proof introduces no additional assertion from the literature.

For an arbitrary base scheme `B`, a commutative group scheme `S`, group schemes
`C` and `G`, and homomorphisms `i : S → C` and `q : C → G`, `rootPointsMap q i a T`
is the homomorphism from the `T`-points of the actual subgroup `subgroup i a` to
those of `subgroup (i ≫ q) a`. Its underlying map is composition with `q`.
Functoriality of the full torus orbit and its zero value proves that this map
lands in the target root subgroup.

`IsOrbitExtension.hasLimit_of_power` is an auxiliary arbitrary-base result. If
`ν : Gm → S` satisfies `ν ≫ a = (t ↦ t^m)` for a positive natural number `m`, an
extension of the full torus orbit through `a` pulls back along the affine map
`t ↦ t^m` to a dynamic orbit extension for `ν ≫ i`. This map fixes zero, so the
dynamic limit is exactly the zero value of the original extension.

Over any field `k`, assume that `S` is a split torus and `a ≠ 0`. If the source
structure morphism is separated and the full scheme-theoretic kernel of `q` is
central, `rootPointsMap_injective` proves injectivity for every test scheme
`T` over `k`, including nonreduced tests. Choose a cocharacter pairing positively
with `a`; root subgroup points then lie in its contracting subgroup. The proved
triviality of the intersection of that contracting subgroup with the full
central kernel gives injectivity. Neither a central isogeny nor separatedness of
the target is needed for this injectivity result.

For surjectivity, assume that `C` and `G` are separated schemes and `q` is a
central isogeny. Here the existing central-isogeny predicate requires the actual
map to be finite, flat, surjective and locally of finite presentation, with its
full kernel central. `exists_root_lift` lifts each rational target root point
to a rational source root point. The proof is as follows.

1. A positive cocharacter places the target point in a contracting subgroup.
   The contracting-point lifting theorem gives a rational source lift `x` in
   the corresponding source contracting subgroup.
2. The entire commutative torus preserves that contracting subgroup. Thus every
   pullback of the full torus orbit of `x` is still contracting. Whenever two
   test maps have the same image under the character, their orbit values have
   the same image under `q`, because the target point has a root orbit extension.
   All-test injectivity on contracting points makes these source orbit values
   equal.
3. The nonzero character of a split torus is quasi-compact, flat and surjective.
   Its product with the test scheme is therefore an effective epimorphism of
   schemes. The preceding equality descends the source orbit to a curve on
   `Gm`, over the original base. Cancelling that epimorphism proves that the
   descended curve maps to the restriction of the target root extension.
4. Finiteness makes `q` proper. The proved affine-line extension theorem over a
   field extends this punctured curve across zero, preserving its composite
   with `q`. The descended factorization makes the resulting curve a full
   torus orbit extension of `x` through the actual character `a`.
5. Pulling the curve back along the positive cocharacter gives a dynamic limit
   with the same zero value. Uniqueness of dynamic limits compares it with the
   identity limit of the chosen contracting lift, so its zero value is `1`.
   This proves membership in the actual source root subgroup.

`rootPointsMap_surjective` packages this rational lift. Together with all-test
injectivity it defines `centralIsogenyRootPointsEquiv`, a multiplicative
equivalence on the test `Spec k → Spec k`. The final coercion lemma states that
its forward map is exactly composition with the original `q`. The field and
all schemes have arbitrary universe `u`. No primitivity of `a`, smoothness of
the kernel, perfectness of the field, smoothness or reductivity of the ambient
groups, or assertion that `a` occurs in the relative root support is assumed.

Surjectivity is asserted only for rational points; there is no all-test
surjectivity claim. The acting split torus and its map to the source are
supplied. This module does not construct a lifted maximal split torus, identify
root supports or valuations for different acting tori, compare apartments, or
prove the final normalizer-image theorem.
