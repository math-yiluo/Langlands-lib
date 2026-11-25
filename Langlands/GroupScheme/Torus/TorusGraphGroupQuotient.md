# The group quotient obtained using the smooth graph relation

This module is the group-scheme continuation of `TorusGraphSchemeQuotient`
on the valuative-lifting route to the affineness of the quotient by the
normalizer of a self-centralizing maximal torus in a smooth separated group.
All schemes are relative to an
arbitrary base `S`. No affineness assumption is imposed on `G` or on the
constructed quotient.

## The fppf group projection

Write `p : G ×ₛ D ⟶ Q` for the smooth surjective graph quotient, and
`j : Q ⟶ L` for its monomorphic map to the ambient group. They satisfy
`j(p(g,d)) = ρ(g)e(d)` as relative scheme maps. Define `quotientMap` to be
`q(g) = p(g,1)` and `torusMap` to be `r(d) = p(1,d)`. Their composites with
`j` are `ρ` and `e` respectively.

`quotientMap_isPullback` computes the base change of `q` along `p`:

```text
       G ×ₛ T  ─── id × π ───▶ G ×ₛ D
          │                     │
    (g,τ) ↦ g t(τ)              p
          │                     │
          ▼                     ▼
          G   ─────── q ──────▶ Q
```

On a relative test, a compatible pair `((g,d),x)` satisfies
`ρ(g⁻¹x) = e(d)` after composing with `j`. The graph-coordinate lemma gives
`τ` with `t(τ) = g⁻¹x` and `π(τ) = d`; monicity of `t` makes this `τ`
unique. This proves the universal property, not only a statement about
geometric points. The top map is a base change of the fppf map `π`, so
`quotientMap_fppf` descends flatness, surjectivity and local finite
presentation along the smooth quasi-compact surjection `p`.

## The descended group

For `groupFactorization`, suppose that `T` is smooth and that `G` and `D`
are smooth and quasi-compact over `S`, with `L` separated over `S`. As in the
scheme construction, `t` represents its own centralizer, `ρ` has central
kernel on all relative scheme tests, and `ρ t = e π` with `π` fppf and `e`
monomorphic. Then `Q` is separated by the monomorphism to `L`. Surjectivity of
`p` and quasi-compactness of the source give quasi-compactness over `S`;
separatedness of `Q` ensures quasi-compactness of `p`. The smooth source
and smooth surjective `p` give smoothness of `Q` over `S`.

The image of the unit of `G` gives the unit lift to `Q`. The multiplication
of `L` on two images of `Q` factors through `j` after the fppf cover
`q ×ₛ q`: on that cover the lift is the product in `G` followed by `q`.
Similarly the inverse of `L` factors through `j` after `q`, with lift
provided by inversion in `G`. The factorization lemma `exists_factor_of_fppf`
descends these lifts. `GroupObjectDescent.grpObjOfMono` then restricts the
group law of `L` along `j`. The scheme maps `q` and `r` preserve the group
laws because they do after composing with `j`.

`groupFactorization` chooses this `GroupFactorization` data, which retains
the smooth surjection `p`, the fppf group homomorphism `q`, the monomorphic
group homomorphism `j`, the image-torus map `r`, and all three factorization
equations. `GroupFactorization.torus_comp` gives `π ≫ r = t ≫ q` by
cancellation through `j`, and `GroupFactorization.isClosedSubgroup_torus`
shows that `r` is closed if `e` is. This is an internal proof construction
using the graph quotient and fppf descent; it does not prove maximality,
closed-fibre conjugacy, or valuative lifting.
