# Central norm inputs from actual vector-group homomorphisms

This internal module supplies the input bridge for the existing polynomial
Galois norm construction. Let `k, L : Type u` be fields with an algebra structure
`k → L`, let `G/k` be a group scheme, and write `G_L` for its actual scheme base
change. An actual homomorphism `f : G_a,L^n → G_L` with the unchanged full-center
predicate `IsCentral f` supplies a central additive polynomial point of `G` over
`L[X_1, …, X_n]`. The bridge works in every characteristic, over finite or
imperfect fields, without dividing by the extension degree.

`vectorCoordinates_aeval` identifies the coordinates of the spectrum map
classified by a tuple. `isAdditive_hom` uses this to identify the universal sum
point with the product of the two universal vector points. Composing with an
actual group-scheme homomorphism proves precisely the existing `IsAdditive`
identity. This is an identity on the polynomial algebra of two independent
tuples; it does not rely on checking field-valued points.

`evaluate_evaluate` proves the composition law for substitution.
`isAdditive_scalar` applies that law and distributivity to show that replacing
each variable `X_i` by `a X_i` preserves additivity. `scalarHom` uses the existing
`homOfAdditive` construction to give the corresponding actual endomorphism of
the vector group. `scalarHom_hom` identifies its underlying morphism with the
spectrum map of this linear substitution.

`substituteAlg_restrictScalars` identifies the norm construction's substitution
of base-field polynomials with ordinary `L`-algebra evaluation after restricting
scalars to `k`. The identity is proved on constants and variables.
`affineBaseChangeEquiv_substitute` combines it with the existing naturality of
`Lie.affineBaseChangeEquiv`.

`affineBaseChangeEquiv_mem_center` transfers full-center membership from an
actual `G_L` point to the corresponding `G` point over the same `L`-algebra. It
uses `center_baseChange` and pulls the center point back along the affine test
comparison isomorphism. Thus it preserves centrality against all refinements
and all comparison points, including nonaffine tests. `centralInput` applies
this result to the underlying morphism of `f`. `centralInput_val` states its
exact underlying polynomial point. `centralInput_mem_additive` transfers the
universal additive identity through the affine comparison and proves membership
in the existing `centralAdditivePoints k G L n` subgroup.

`scalarCentralInput` precomposes `f` by `scalarHom a` for any `a : L`, then applies
`centralInput`. Its value formula says explicitly that the scalar acts on the
extension-field polynomial point before any Galois product or descent. Every
scalar gives a valid central additive input. No affineness, finite-dimensionality
or Galois hypothesis is needed for these input constructions.

Assume now that `G.X.left` is affine and `L/k` is finite Galois.
`normOfCentralHom f hf a` applies the existing `centralNormHom` to the scaled
input and gives an actual homomorphism `G_a,k^n → G`. The theorem
`normOfCentralHom_isCentral` proves its full centrality, and
`normOfCentralHom_extension` identifies coefficient extension of its underlying
polynomial morphism with the full product over the coefficient conjugates of
the scaled input. These results directly reuse the proved norm construction.

Finally, `normOfCentralVector` accepts an actual `L`-group `V` equipped with the
existing natural all-test vector coordinates `e` and an actual central
homomorphism `z : V → G_L`. It uses the inverse of `vectorGroupIso e he` to
supply the standard-vector input to `normOfCentralHom`. The theorem
`normOfCentralVector_isCentral` retains full centrality. The construction does
not require `z` to be a closed immersion or `n` to be positive; these additional
hypotheses are relevant to future nontriviality arguments.

The provenance is internal: the module combines actual vector-group
corepresentation, the universal additive identity, the existing affine
base-change comparison, full-center base change, and the previously constructed
polynomial norm. It asserts no nontriviality for any scalar parameter, no
nonzero tangent, no split-unipotence descent and no maximal-torus conjugacy.
Those remain separate proof obligations.
