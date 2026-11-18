# Short exactness of the absolute-Galois character functor

`Langlands.GroupScheme.multiplicativeTypeAbsoluteExactness` proves
`Langlands.GroupScheme.MultiplicativeTypeAbsoluteExactnessStatement.{u}`.
It is the short exact sequence clause of Milne, *Algebraic Groups* (2017),
§12.g and Theorem 12.23, pp. 239–240, for the actual absolute-Galois
character functor. The registered source is `milne-2017-algebraic-groups`.

For a field `k`, extend the three groups to `Ω = SeparableClosure k`.
The published algebraic base change and separably closed diagonalizability
results give each group a diagonalizable model with finitely generated
abelian character group. `fieldExtension_fpqc` makes the base map fpqc.
The model isomorphisms transport both maps, and
`DiagonalizableCharacter.restrictMap_bijective` expresses the transported
maps as `D(f)` and `D(g)` for maps `f : ME →+ MN` and `g : MQ →+ ME` of the
model character groups.

The proof applies `MultiplicativeTypeGaloisExactness.descent_iff` and
`transport_iff` to carry the closed immersion and represented fppf
quotient conditions to the split models. `splitCore` identifies these
conditions with injectivity of `g`, exactness of `g, f`, and surjectivity
of `f`. The quotient predicate retains local finite presentation and the
full kernel comparison on every test scheme, along with flatness and
surjectivity of the underlying scheme map.

The evaluation-character equivalences and the model isomorphisms give a
commuting ladder between the model characters and the actual characters
over `Ω`. On the actual characters, `Preadditive.leftComp` gives the
same functions as the underlying linear maps of `characterFunctor`,
by precomposition with the base-changed group homomorphisms.
The evaluation formula `restrictHom_comp_evalCharacter` proves commutativity, so
`Function.Exact.iff_of_ladder_addEquiv` transports exactness and the same
additive equivalences transport injectivity and surjectivity. The maps are
already morphisms in the finitely generated discrete Galois module category.

This uses the published split argument for Milne's Theorem 12.9(b),
pp. 233–234, at `Ω`, including its treatment of torsion. The target holds
in every universe and over every field for all objects of
`MultiplicativeTypeGroup k`, including finite nonsmooth groups.
