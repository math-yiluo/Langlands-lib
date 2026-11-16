# Underlying scheme solutions and quotient maps

This internal construction concerns arbitrary schemes `B,S` in universe `u`,
a map `p : S ⟶ B`, an actual group scheme `G` over `S`, and an actual Čech
datum `D : Datum p G`. It generalizes the underlying-solution interface in
`AffineDatumScheme` by omitting the affineness field. It does not construct
an underlying quotient for an arbitrary datum.

`SchemeSolution D` supplies an object `obj : Over B`, a scheme morphism
`proj : G.X.left ⟶ obj.left`, the pullback square with sides
`G.X.hom`, `proj`, `p`, and `obj.hom`, and the relation equation
`D.source ≫ proj = D.target ≫ proj`. There is no affineness, separation,
quasi-compactness, smoothness, or finite-type hypothesis in this structure.

The supplied square gives the slice isomorphism `s.iso : p*s.obj ≅ G.X`.
Its two projection formulas express compatibility with the actual quotient
map. `kernelPair` proves that `D.source,D.target` form the complete
scheme-theoretic kernel pair of `s.proj`: paste the target pullback square
with the square defining the overlap, then cancel the supplied quotient
square. A kernel-pair lift consequently proves `comp_eq_of_proj_eq` for
every test scheme.

Flatness, surjectivity, quasi-compactness and étaleness of `p` each transfer
individually to `s.proj` by base change. Under `[Etale p] [Surjective p]`,
the quotient map is an effective epimorphism, using Mathlib's fppf
effective-epimorphism instance. Thus `desc` factors every relation-invariant
scheme map through the quotient; `desc_fac` gives recovery and `desc_unique`
gives uniqueness by epimorphism cancellation. This uses no
quasi-compactness assumption on `p`.

Conversely, every supplied group-scheme solution `t : Solution D` gives a
`t.schemeSolution : SchemeSolution D`, without geometric assumptions on `p`.
Its quotient map `t.schemeProj` is the inverse of `t.iso` followed by the
first pullback projection. Transport of the canonical pullback square proves
`schemeProj_square`. Compatibility of the inverse isomorphism, followed by
the original-group projection, proves `schemeProj_relation`, since canonical
overlap transport preserves that projection.

The provenance is internal: the arguments adapt the published
`AffineDatumScheme` interface and use the actual `DatumRelation` and `Data`
definitions together with Mathlib's pullback and effective-epimorphism APIs.
There is no additional literature assertion or effectivity axiom. The
arbitrary-base construction of the supplied underlying solution remains a
separate obligation.
