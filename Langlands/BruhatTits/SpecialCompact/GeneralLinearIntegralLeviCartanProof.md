# Block Cartan decomposition in the inherited integral Levi of `GL_N`

`Langlands.BruhatTits.SpecialCompact.generalLinearIntegralLeviCartan` proves
`GeneralLinearIntegralLeviCartanStatement.{u}` at arbitrary universe `u`.
For `GL_N` over a nonarchimedean local field `F`, a generic diagonal
cocharacter `ν` and a subset `J` of its simple relative roots, let `KJ` be
the preimage of the standard integral points `GL_N(𝒪_F)` in the rational
points of the actual standard Levi `M_J`. Let `iJ` be the diagonal torus
factored through `M_J`. Evaluating at the shared order-one uniformizer the
cocharacters `c` with `⟨α, c⟩ ≥ 0` for every positive root `α` of `iJ`
(positivity is measured by `ν`) gives one representative of each
`KJ`-double coset of `M_J(F)`. This is the Cartan clause of Renard,
Theorem V.5.1(5), as it applies part (4), with the representative set of
V.3.23, for the standard integral subgroup of every standard Levi of `GL_N`.
[Statement](GeneralLinearIntegralLeviCartanStatement.md)

## Implemented proof

**Weight blocks.** The published `standardCocharacter` provides a standard
cocharacter `ζ` for the index `J`. Write `w` for its diagonal weights and `s`
for those of `ν` (`GeneralLinear.cocharacterCoordEquiv`). The blocks are the
fibres of `w`, labelled by the finite image of `w`. The published
`generalLinearStandardLeviIntegralPoints` identifies the matrices of
`M_J(F)` with `GeneralLinear.blockLeviSubgroup F w`. These are the
invertible matrices with zero entries between coordinates of different
weights. It also identifies the image of `KJ` with the entrywise image of
`GeneralLinear.blockLeviSubgroup 𝒪_F w`.
[Inherited integral points](GeneralLinearStandardLeviIntegralPointsStatement.md)
[Standard cocharacters](../../GroupScheme/Rational/StandardCocharacterProof.md)

**The block equivalence.** For every commutative ring `A`, the private equivalence
`blockEquiv` takes a block diagonal invertible matrix to the family of its
diagonal blocks. The `b`-block of a product of block diagonal matrices is the
product of the `b`-blocks, because the off-diagonal blocks vanish. So the
`b`-block of the inverse is an inverse of the `b`-block. In the other
direction, `Matrix.blockDiagonal'` assembles a family of blocks. It is
reindexed along `Equiv.sigmaFiberEquiv` from the disjoint union of the
blocks to `Fin N`. Inside the block `b`, the coordinates are ordered by
decreasing values of `s`: `blockOrder` sorts them with `Tuple.sort`. Since
`ν` is generic, `s` is injective
(`GeneralLinear.isGenericCocharacter_diagonalTorus_iff`), so `s` is
strictly antitone in this order. This gives `sortedBlockEquiv`, valued in
`∏_b GL_{n_b}(A)` with `n_b` the size of the block `b`. It commutes with
the entry map `𝒪_F → F`. Hence a Levi point lies in `KJ` exactly when each
of its sorted blocks lies in the image of `GL_{n_b}(𝒪_F)`
(`Iwasawa.integralRange`).

**Uniformizer points.** The proof factors the uniformizer point of `c`
through `Standard.leviTorusHom_comp`. Then the published
`rationalPointsEquiv_diagonalUniformizerSection` shows that its matrix is
the diagonal matrix `Iwasawa.torus π (weights of c)`. Here `π` is the
uniformizer of the shared section; `uniformizerUnit_isUniformizingElement`
checks that it satisfies the matrix Cartan theorem's value-group condition.
So its sorted `b`-block is the diagonal matrix of the powers of `π`, with
the weights of `c` read in the order of the block.
[Ambient uniformizer comparison](GeneralLinearIntegralCartanProof.md)

**The chamber condition.** The standard Levi represents the dynamic
centralizer of `ζ`. By the published `dynamicCentralizerReductive` it is
connected reductive, hence smooth. Then `relativeRoots_centralizer_factor`
identifies the roots of `iJ` with the roots of the diagonal torus of `GL_N`
that pair to zero with `ζ`. The roots of `GL_N` are indexed by ordered pairs
`(p, q)` of distinct coordinates, and pair with `c` as `c_p − c_q`
(`GeneralLinear.latticePairing_rootDatum_root_fintype`). So the positive
roots of `iJ` are the pairs with `w p = w q` and `s q < s p`. They join two
coordinates of the same block, the first one earlier in the sorted order.
Therefore the chamber condition on `c` holds exactly when, in every block,
the sorted weights of `c` form an antitone tuple.
[Roots of standard Levis](../../GroupScheme/Rational/StandardLeviStandardFamiliesProof.md)
[Dynamic centralizers are reductive](../../GroupScheme/Dynamic/CentralizerReductiveProof.md)

**Injectivity.** Suppose that the uniformizer points of two chamber
cocharacters `c` and `d` lie in the same `KJ`-double coset. Applying the
`b`-component of `sortedBlockEquiv` gives a matrix double coset equality in
`GL_{n_b}(F)`, with integral factors. Both exponent tuples are antitone, so
`Cartan.exponent_unique` makes them equal. This holds in every block, and
every coordinate lies in exactly one block. So `c` and `d` have the same
weights, and `c = d`.

**Surjectivity.** Given `g ∈ M_J(F)`, apply `Cartan.exists_cartan` to each
sorted block of `g`. This gives an antitone exponent tuple `a_b` and
integral matrices `k_b` and `l_b` with block `b` of `g` equal to
`k_b · torus(a_b) · l_b`. `GeneralLinear.cocharacterOfWeights` assembles
the tuples, through the equivalence of the disjoint union of the sorted
blocks with `Fin N`, into one cocharacter `c`. Its sorted block weights are
the `a_b`, so it lies in the chamber. The inverse of `sortedBlockEquiv`
turns the families `(k_b)` and `(l_b)` into two elements of `KJ`. Their
product with the uniformizer point of `c` is `g`.
[Matrix Cartan theorem](../../Group/GL/CartanProof.md)

## Provenance and scope

The proof reduces the Levi to products of general linear groups and applies
the matrix Cartan decomposition block by block. It does not follow Renard's
argument through the building and the affine Weyl group. The theorem uses
only the standard integral model of `GL_N`. It imposes no restriction on the
characteristic or residue characteristic of `F`, on `N` or on `J`. Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.
