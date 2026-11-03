# Fixed-lattice targets for the actual norm-one torus

This file specifies a focused proof target over the published norm-one group
scheme and its ordinary Galois lattice comparisons. It contains proposition
definitions, not proofs of those propositions.

Let `k`, `K` and `Ω` be fields in the same universe, with specified `k`-algebra
structures on `K` and `Ω`. The aggregate target
`Langlands.GroupScheme.WeilGm.normOneGaloisFixedLatticesStatement k K Ω`
assumes finite dimensionality of `K/k` as a typeclass and explicitly takes the
following premises: `K/k` is separable, `Ω/k` is normal, and every minimal
polynomial of an element of `K` splits after mapping its coefficients to `Ω`.
Normality is Mathlib's field-extension normality; no finite-dimensionality
assumption on `Ω/k` is made. There is no specified algebra structure `K → Ω`;
the coordinate set is the set of all `k`-algebra embeddings `K →ₐ[k] Ω`.

The conclusion is the conjunction of five named propositions:

1. `embeddingActionTransitiveStatement` says that for any two embeddings
   `τ` and `υ` there is a `k`-automorphism `σ` of `Ω` with `σ ∘ τ = υ`.
2. `embeddingSumZeroFixedStatement` says that a sum-zero integer function on
   the embedding set is fixed by every coefficient automorphism if and only
   if it is zero.
3. `embeddingQuotientFixedStatement` makes the same assertion for a class
   of integer functions modulo constant functions. Its premise is invariance
   of the quotient class, without assuming that a chosen representative is
   invariant.
4. `normOneCocharacterFixedStatement` says that an actual cocharacter of the
   base change to `Ω` of the norm-one group is fixed by every coefficient
   automorphism if and only if it is the zero cocharacter.
5. `normOneCharacterFixedStatement` gives the corresponding assertion for
   actual characters.

The five component definitions merely name their conclusions. When used on
their own they do not carry the aggregate target's separability, normality and
splitting premises. The coordinate sum and its kernel use finite
dimensionality to obtain the finite embedding set.

The coordinate actions are the published inverse-pullback permutation action,
its restriction to the kernel of `embeddingCoordinateSum`, and its induced
action on the quotient by `embeddingDiagonal`. The actual actions are
`cocharacterLattice.galoisRepresentation` and
`characterLattice.galoisRepresentation` on the actual base-changed
`normOneCommGroupScheme`. These are the ordinary actions on actual morphisms.
The quotient is a quotient of integer lattices; the group scheme itself remains
the actual kernel of the norm morphism.

The provenance is internal: this target isolates the elementary fixed-vector
calculation needed after the published constructions in
`WeilRestrictionNormOneCocharacters` and `WeilRestrictionNormOneCharacters`.
The intended proof route extends isomorphisms of embedded subfields using
normality, proves that invariant coordinate functions are constant, and uses
the finite integer coordinate sum to handle both sum-zero vectors and
invariant classes modulo constants. The published equivariant additive
equivalences then transfer vanishing to the two actual lattices. This route is
an explanation of the proposed target, not proof evidence.

The target asserts neither rational descent of morphisms nor an anisotropy
criterion for the actual group. Such consequences require their separate
descent and comparison results.
