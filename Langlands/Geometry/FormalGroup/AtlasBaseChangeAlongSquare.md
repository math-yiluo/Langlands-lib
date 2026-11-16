# Actual formal comparison for commuting coefficient squares

This internal construction uses `AtlasRationalBaseChangeAlongComposition`.
It composes the specified actual composition isomorphisms and transports along
an equality of composite coefficient maps. Its provenance is the existing
formal atlas infrastructure; it makes no new original-literature assertion.

Let `O` be a commutative ring and `R`, `S`, `S'`, `T` commutative
`O`-algebras in one universe `v`. Let

```text
f : R →ₐ[O] S       g : S →ₐ[O] T
p : R →ₐ[O] S'      q : S' →ₐ[O] T
e : g.comp f = q.comp p.
```

The atlas `X : BasicAtlas O R σ` has a finite coordinate type `σ` and may
have an infinite principal cover. Comparison naturality allows a second atlas
`Y` with a different finite coordinate type and the same original cover.
Tests have universe `v`; complete compatible families have universe `v+1`.
No flatness or injectivity condition is imposed on these four maps.

The existing `baseAlongMapOpens_eq`, imported from
`AtlasRationalBaseChangeSelf`, preserves equality of original covers under the actual
image of a supplied coefficient map. `baseAlongEqOpens_eq` identifies image
covers of equal supplied maps. `baseAlongEqIso X e` is an actual atlas
isomorphism between extension along the two equal maps. It is defined by
equality elimination, after which it is exactly `Iso.refl`. The accompanying
`baseAlongEqPointEquiv` transports original complete families between the
two restricted coefficient tests, and `baseAlongEq_onPoints` proves that the
actual identity transport realizes this entire-family equivalence. The two
`Hom.baseAlongEq_*natural` laws state naturality of its forward and inverse
maps; eliminating `e` reduces them to the formal identity laws.

`baseAlongSquareOpens_eq X f g p q e` identifies the actual successive image
covers `g '' (f '' X.opens)` and `q '' (p '' X.opens)`. It composes the
left composition-cover equality, the equality induced by `e`, and the reverse
right composition-cover equality. `baseAlongSquareIso` constructs the actual
formal isomorphism

```text
(X.baseChangeAlong f).baseChangeAlong g
  → (X.baseChangeAlong p).baseChangeAlong q
```

as the following composite, with the arrows applied from left to right:

```text
baseAlongCompIso X f g ; baseAlongEqIso X e ; (baseAlongCompIso X p q)⁻¹.
```

Thus both maps are formal maps on every localized coefficient test, natural
in coefficients and compatible with overlaps, and they satisfy both formal
inverse equations. They retain the actual charts and transition series of
the supplied-map composition isomorphisms. The construction is not merely a
comparison of point functors.

For a `T`-test `A` and an original complete family `x` on restriction along
`g.comp f`, `baseAlongSquare_onPoints` says that extending `x` along `f`
and then `g`, and applying the displayed formal isomorphism, gives extension
along `p` and then `q` of the family transported by
`baseAlongEqPointEquiv e A`. It compares the full compatible families on all
further tests. The proof uses the point maps of formal composition, the two
existing composition-family equations, and the equality-transport equation.
`baseAlongSquare_inv_onPoints` proves the reverse equation for the same
linear equivalence, using its inverse law.

`Hom.baseAlongSquare_natural` states that for every actual integral map
`a : Hom X Y h`, extending `a` along `f,g` and then applying the target
square comparison equals applying the source square comparison and then
extending `a` along `p,q`. `baseAlongSquare_inv_natural` gives the reverse
square using the actual inverse. In each proof the four extended maps are
first given explicit types over the supplied target scalar structures. The
left composition naturality equation, equality-transport naturality equation
and reverse right composition equation then combine by associativity.
The reverse proof uses the corresponding three inverse equations.

For a field `F` with an `O`-algebra structure, rational Hom is the entire
global tensor `F ⊗[O] BasicAtlas.Hom`. The two
`RationalHom.baseAlongEq_*natural` laws hold on every such tensor by equality
elimination and the rational identity laws.
`RationalHom.baseAlongSquare_natural` and `baseAlongSquare_inv_natural`
give the forward and reverse square equations for every global tensor.
The comparison maps are the rationalizations of the actual formal maps just
constructed. The proofs give explicit supplied-target types to the four
extended tensors, expand rationalization of the composed integral comparison
maps, and combine the existing rational composition and equality naturality
laws by rational associativity. No chart-evaluation injectivity or local
rational gluing premise is used.

For quasi-isogenies, additionally assume that `O` is a domain and `F` is its
fraction field. `baseAlongSquareQuasiIsogeny` applies `QuasiIsogeny.ofIso`
to the actual square isomorphism, retaining both rationalized maps and both
inverse equations. Its `_hom` and `_inv` lemmas expose these maps.
`QuasiIsogeny.baseAlongSquare_natural` and `baseAlongSquare_inv_natural`
are equalities of whole quasi-isogenies. They follow by forward-map
extensionality from the corresponding rational equations, so their inverses
are identified as well.

This pair concerns the specified square and its actual comparison. Full-order
equivariance and specialization to the natural quotient square of varying
nilpotent coefficient algebras are subsequent interfaces. Arbitrary-refinement
invariance, identity or higher coherence, height, framing, polarization,
descent, levels and representability are outside its claims.
