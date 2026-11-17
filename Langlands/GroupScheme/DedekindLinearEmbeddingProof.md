# Closed linear embeddings over Dedekind domains

The theorem `Langlands.GroupScheme.dedekindLinearEmbeddingStatement.{u}` proves
the unchanged Library proposition
`Langlands.GroupScheme.DedekindLinearEmbeddingStatement.{u}` for every universe
`u`. For every Dedekind domain `R` and every group scheme `G` over `Spec R`
whose structure morphism is flat, affine and locally of finite type, it
constructs a natural number `N` and a group-scheme morphism
`ρ : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup ρ`. The latter
means that the underlying morphism of schemes is a closed immersion.

## Source and provenance

The mathematical target is Brian Conrad, *Reductive group schemes* (2014),
Exercise 5.5.7(ii), printed p. 184, source ID
`conrad-2014-reductive-group-schemes`. The retained source is
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`,
SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The exercise suggests using finite torsion-free modules as direct summands
of finite free modules. The proof below implements that suggestion.

The split-coaction extension and its finite-basis coefficient lemmas are
internal constructions for this proof. The coefficient computations adapt
the published `IntegralLinearEmbedding.Comodule` computations from a free
submodule of the coordinate algebra to an arbitrary finite free comodule.
The final affine-scheme transport adapts
`IntegralLinearEmbedding.ClosedEmbedding`. Both published modules are
imported without modification; their PID-specific existence theorems are
not used to deduce the Dedekind case.

## Extending a split coaction

For a commutative `R`-bialgebra `B`, `contractCounit` is the linear map
`V ⊗[R] B → V` given by `v ⊗ b ↦ ε(b) • v`. Its naturality with respect
to a linear map in the first factor is proved by tensor induction.

Suppose `δ : V → V ⊗[R] B` is a counital, coassociative right coaction,
and `p : F → V`, `i : V → F` satisfy `p ∘ i = id`. Set

```text
D(x) = (i ⊗ id)(δ(p(x))) + (x - i(p(x))) ⊗ 1.
```

This is `extendedCoaction`. The lemmas `extendedCoaction_inclusion`,
`extendedCoaction_complement` and `extendedCoaction_projection` prove,
respectively,

```text
D(i(v)) = (i ⊗ id)(δ(v)),
D(x - i(p(x))) = (x - i(p(x))) ⊗ 1,
(p ⊗ id)(D(x)) = δ(p(x)).
```

The counit identity for `D` follows from the naturality of contraction and
`ε(1) = 1`. To prove coassociativity, the Lean proof compares its two sides
on `i(V)` and on the elements `x - i(p(x))`. On the first summand tensor
naturality reduces the equation to the coassociativity of `δ`; on the
second it reduces to `Δ(1) = 1 ⊗ 1`. Linearity and
`x = i(p(x)) + (x - i(p(x)))` give the identity for every `x`.

## Coefficients of a finite free comodule

For a basis `e : Basis (Fin N) R F`, `coefficientMatrix e D` is the matrix
`M` characterized by

```text
D(e j) = ∑ i, e i ⊗ M i j.
```

The tensor-to-finitely-supported-functions equivalence proves this
expansion and uniqueness of coefficients, with no flatness hypothesis on
the right tensor factor. Applying uniqueness to the coassociativity
equation gives

```text
Δ(M i j) = ∑ l, M i l ⊗ M l j.
```

Taking basis coordinates of the counit identity gives
`ε(M i j) = (1 : Matrix (Fin N) (Fin N) R) i j`.

If `f : F →ₗ[R] B` intertwines `D` with the regular coaction `Δ`, applying
the counit in the first factor of
`Δ(f(e j)) = ∑ i, f(e i) ⊗ M i j` expresses `f(e j)` as a linear
combination of the entries of `M`. Expanding an arbitrary vector in the
basis proves `image_mem_span_coefficientMatrix`: all of `f(F)` is contained
in their `R`-linear span.

## The Dedekind matrix construction

`exists_matrix_coefficients` takes an arbitrary finite subset `S` of a
flat commutative bialgebra `B` over a Dedekind domain `R`.
The published `IntegralLinearEmbedding.finiteSubcomodule_spec` supplies a
finitely generated right subcomodule `Λ ⊆ B` containing `S`.

Flatness over the domain makes `B` torsion-free, hence `Λ` torsion-free.
The Dedekind torsion-free flatness instance makes `Λ` flat. Since `R` is
Noetherian and `Λ` finite, it is finitely presented;
`Module.Flat.projective_of_finitePresentation` makes it projective.
Then `Module.Finite.exists_comp_eq_id_of_projective` gives a finite free
module `F = (Fin N → R)` with a surjection `p : F → Λ` and a section
`i : Λ → F`.

The published `HopfPointWeightWindow.exists_coaction` lifts `Δ` to a
coassociative coaction on `Λ`. Its counit identity follows by applying the
injective inclusion `Λ → B`, naturality of `contractCounit`, and the
coalgebra counit identity on `B`. Extend this coaction to `F` as above.
The composite `f : F → Λ → B` intertwines the extended coaction with `Δ`,
by `extendedCoaction_projection` and the compatibility of the lifted
coaction. Its image is `Λ`, so the finite-basis coefficient argument
gives a matrix with both coalgebra identities and with `S` in the span
of its entries.

## Closed immersion and affine transport

For a flat algebra of finite type that corepresents a group functor,
choose finitely many algebra generators `S`. The preceding construction
gives a matrix whose entries span `S`, hence generate the whole
coordinate algebra as an `R`-algebra. The published
`AffineLinearEmbedding.toGLHom` turns the two matrix coalgebra identities
into a morphism to `GL_N`, and
`AffineLinearEmbedding.isClosedSubgroup_toGLHom` proves that it is a
closed immersion from this algebra-generation property.

For the actual group scheme `G`, affineness gives an affine coordinate
model and an isomorphism over `Spec R`. The published
`AffineCorepresentation.finiteType_of_iso` and
`IntegralLinearEmbedding.flat_of_iso` give the required properties of its
coordinate algebra. Apply the corepresented construction and precompose
the resulting representation with `AffineCorepresentation.toModel`.
The isomorphism and the constructed representation are closed
immersions, so their composite is one. The final theorem unwraps this
embedding into the exact existential conclusion of the published
statement.
