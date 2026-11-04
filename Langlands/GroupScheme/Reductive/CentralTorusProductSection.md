# Surjectivity of a subgroup product from surjectivity onto a quotient

This module supplies one step of the proof that a central torus and the derived
subgroup cover a connected reductive group
(`ReductiveCentralTorusSurjectivityStatement`). It is a derived, purely formal
lemma about group schemes over an arbitrary base `S`; it uses no hypothesis on
fields, smoothness, connectedness or centrality.

## Statements

`surjective_subgroupProductMap_of_kernel_le_of_surjective_comp` takes
homomorphisms `i : Z ⟶ G`, `d : D ⟶ G` and `q : G ⟶ Q` of group schemes over
`S` such that

- every point of the pointwise kernel `SubgroupFunctor.kernel q`, on every test
  scheme over `S`, factors through `i` (`kernel q ≤ range i`), and
- the underlying morphism of schemes of `d ≫ q` is surjective on points.

It concludes that the underlying morphism of schemes of
`subgroupProductMap i d : Z.X ⊗ D.X ⟶ G.X`, the map multiplying the images of
`i` and `d` (in the order `i`-factor times `d`-factor), is surjective on points.
This entry declaration is an internal proof-producing `def` whose type is this
proposition (the `linter.defProp` linter is disabled for it), so that the module
can be published as a definition artifact; it is used exactly like a theorem.

`surjective_subgroupProductMap_of_isFppfQuotient` is the same conclusion when
`q` is a represented fppf quotient with kernel exactly `range i`
(`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`). Only the kernel
part of that hypothesis is used: by `SubgroupFunctor.range_kernelι` the range
of the actual kernel inclusion of `q` is the pointwise kernel, so the kernel
condition above holds with equality.

## Proof

Write `f` for the underlying scheme morphism of `q` and `g` for that of `d ≫ q`.
Let `P` be the fibre product of `f` and `g` in schemes, viewed as a scheme over
`S` through its first projection to `G`. Its two projections give points
`p₁ : P ⟶ G.X` and `p₂ : P ⟶ D.X` over `S`, with
`p₁ ≫ q = p₂ ≫ d ≫ q` by the pullback square.

The point `p₁ * (p₂ ≫ d)⁻¹` of `G` therefore maps to the identity of `Q`, so it
lies in the kernel of `q` and hence equals `z ≫ i` for some point
`z : P ⟶ Z.X`. The point `lift z p₂ : P ⟶ Z.X ⊗ D.X` then satisfies
`lift z p₂ ≫ subgroupProductMap i d = (z ≫ i) * (p₂ ≫ d) = p₁`.

Surjectivity of morphisms of schemes is stable under base change, so the
first projection of the fibre product, the base change of `g` along `f`, is
surjective. Every point `x` of `G` is thus the image of a point `y` of `P`,
and the image of `y` in `Z.X ⊗ D.X` maps to `x` under the product map.

## Provenance

This is a derived, internal lemma. In J. S. Milne, *Algebraic Groups* (2017),
Proposition 12.46(b) (printed pp.245–246), the conclusion `G = T · D(G)` for a
central torus `T` with `G/T` perfect is obtained by passing to an algebraically
closed field and observing that `G/(T · D(G))` is both commutative and perfect.
The Lean route instead splits the argument into surjectivity of `D(G)` onto
the quotient `G/T` (proved separately) and the fibre-product section argument
above, which works over any base and for all scheme points.
