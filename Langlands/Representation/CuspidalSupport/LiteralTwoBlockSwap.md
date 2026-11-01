# Actual swap to a literal reversed two-block product

This internal transport adapter specializes the published
`irreducibleTwoFactorSwapIso` to the literal shape `(a,b)`, for positive ranks
`a,b`, and identifies its permuted target with the literal product on `(b,a)`.
The two actual smooth factors and the original normalized product must be
irreducible. The ranks need not agree. The supplied field and topological data
are unchanged, and the field and factor-carrier universes are independent.

`irreducibleLiteralTwoBlockSwapEquiv` constructs an actual representation
equivalence from the original product to the reversed product pulled back along
`GeneralLinear.reindex (finCongr (Nat.add_comm a b))`. The proposition
`IrreducibleLiteralTwoBlockSwap` records the existence of precisely that
equivalence, and `irreducibleLiteralTwoBlockSwap` proves it.

The implemented proof first applies the existing actual swap isomorphism.
`twoBlocks_swap_rankCast` identifies the swapped shape, after transporting its
total rank from `a+b` to `b+a`, with the literal reversed shape. Equality at each
of its two slots identifies the transported factor family. The private
`productObj_congr` transports the normalized product along these equalities;
its proof is equality elimination. Finally,
`normalizedProductInducedRankCastEquiv` identifies induction over the
rank-transported shape, pulled back along the entry-preserving reindex, with the
original induction. Its inverse and the factor-family identification complete
the equivalence.

The provenance is internal composition of existing actual induction and
rank-transport interfaces. The mathematical commutativity input is entirely
the published `irreducibleTwoFactorSwapIso`; this adapter adds no
irreducibility theorem for a reducible product. It supplies neither of the
ambient repeated-factor Jacquet transfers.

The recursive import audit at Library base
`765890b9608eacc70735a6075db0c5299022532d` contains 638 project modules.
The 637 imported modules are byte-identical to that base; only this entry is
new, and every module has its Markdown companion. The used commutativity
route was checked through
`Classification.twoFactorProductConstituentCommutativity`,
`RepresentationExactComparison.nonempty_equiv_of_sameFactors`,
`Classification.irreducibleProductFiniteLength`, and the individual cuspidal
embedding and cuspidal-induction-length proofs. Commutativity uses inverse
transpose, smooth induction duality, and Gelfand--Kazhdan on simple factors.
Finite length comes from actual blockwise cuspidal embeddings, ordered
induction in stages, and detection of nonzero subquotients by minimal nonzero
Jacquet modules and the associated geometric filtration. These are individual
embeddings and actual length bounds; no global decomposition by cuspidal lines,
general ordered quotient coverage, strong-head or multisegment classification,
tempered uniqueness, or square-integrable or regular exhaustion conclusion is
used. The only added transport of induction is the explicit function
precomposition in `normalizedProductInducedRankCastEquiv`. The private
shape-and-family equality helper follows the equality-elimination pattern
already used in `CuspidalSupport.AdjacentInnerBinaryBridge`.
