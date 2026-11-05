# Root subgroup transport through a supplied central-cover diagram

This is a derived comparison of the existing full-torus root subgroup functors.
It combines orbit reparametrization with the central-isogeny equivalence on
rational root points. No new assertion from the literature is introduced.

Over an arbitrary base scheme `B` in universe `u`, let `S' → S` be a homomorphism
`τ` of commutative group schemes whose underlying scheme morphism is flat and
surjective. Let `i : S → G` be any group homomorphism and `a : S → Gm` any
character. For every test scheme `U`, point `g` and affine-line curve `v`,
`isOrbitExtension_precomp_torus_hom_iff` proves that `v` extends the full orbit
of `g` for `(i,a)` if and only if it extends that orbit for `(τ ≫ i, τ ≫ a)`.
The curve itself is unchanged. The forward reparametrization law was already
proved in `CrossTorusRootTransport`. To reflect the law, the proof uses that
`U × τ` is flat and surjective by base change, hence an epimorphism of schemes
and of the category of schemes over `B`. Cancelling it in the extension
equation gives the original law.

The value of `v` at zero is also unchanged. Consequently,
`subgroup_precomp_torus_hom` identifies the two actual subgroup functors on
every scheme test, including nonreduced tests. There is no requirement that the
acting groups be tori, that the character be nonzero or primitive, or that the
ambient group be separated or reductive. Quasi-compactness and local finite
presentation of `τ` are unnecessary for this equality.

`comp_mem_subgroup_of_flatSurjective_transport` applies this equality to a
commuting square of group homomorphisms. If `j : S' → H` and `f : H → G`
satisfy `j ≫ f = τ ≫ i`, then composition with the actual `f` takes every
`U`-point of `subgroup j (τ ≫ a)` to a `U`-point of `subgroup i a`.
This conclusion holds on all tests.

For the rational equivalence, let `k` be any field, `C` and `G` separated
schemes with group structures over `k`, and `q : C → G` a central isogeny
in the existing finite, flat, surjective, locally finitely presented convention,
with full central kernel. Supply a split commutative group scheme `S`,
a commutative group scheme `T`, homomorphisms `i : S → C`, `j : T → G`
and a flat surjective `τ : S → T` such that
`i ≫ q = τ ≫ j`. For each nonzero character `a` of `T`,
`centralIsogenyRootTransportEquiv` gives a multiplicative equivalence
between the rational points of `subgroup i (τ ≫ a)` and `subgroup j a`.
Only `S` is required to be a split torus. Flat surjectivity makes character
pullback injective, so `τ ≫ a` is nonzero. The central-isogeny root equivalence
first identifies the source root points with those for `(i ≫ q, τ ≫ a)`;
the commuting square and the all-test reparametrization equality then identify
the latter subgroup with `subgroup j a`. The coercion lemma proves that the
forward map is exactly composition with `q`.

Surjectivity of the central-isogeny comparison is asserted only at the rational
test `Spec k → Spec k`. All schemes and the field have arbitrary universe `u`.
The comparison uses a supplied diagram; it does not construct the split tori
or their maps, prove that a character occurs in a root support, compare
valuations or apartments, or prove the final normalizer-image theorem.
