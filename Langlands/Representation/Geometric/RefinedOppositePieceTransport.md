# Flattened inner reversal and opposite whole-target pieces

This internal construction expresses the published full refined-Levi
reversal in flattened product-Levi coordinates and compares an actual
reversed upper geometric piece with transport of the original inner
opposite Jacquet module. It uses the actual blockwise permutation,
ambient embeddings, normalized quotients, and geometric-piece functor.
It is a prerequisite for the supported branch obstruction, not a proof
of that proposition.

`innerReversePermutation` assembles the reversal permutation of each inner
shape inside its coarse block. `flattenedRefinementReverseEquiv` passes from
the original flattened Levi to its refined subgroup, reverses all inner
block labels, and returns to the reversed flattened Levi.

`innerReverse_conj_embedding` identifies this map with inverse conjugation
by the assembled permutation. The proof uses
`ProductLeviMinimalIndex.leviEmbedding_conj_blockPermOf`, the published
`reverseWeyl_mul_refinedLeviReverseEquiv`, and both flattened embedding
identities. Surjectivity gives `conjugatesLevi_innerReverse`; injectivity of
the ambient Levi embedding identifies inverse `leviConjugation` with the
constructed equivalence.

For compatible p-adic topological data,
`flattenedNormalizedOppositeReverseEquiv` pulls back the published
`normalizedRefinedOppositeReverseEquiv` along the original flattened
coordinates. The inverse-conjugation identity just proved identifies its
source with Weyl transport by the actual inner reversal. Consequently the
normalization is inherited from the proved full refined-Levi equivalence,
including its opposite half-modulus factor.

Write `b` for the inner reversal permutation. For any `x` conjugating
`B.flatten S` onto `C`, `reversedPiecePermutation` is
`C.reversePermutation⁻¹ * (x * b)`. Its conjugacy from the reversed
flattened source to `C.reverse` is the composite of the actual inner
reversal conjugacy, the supplied `x` conjugacy, and inverse target
reversal.

`reversedWholeLeviGeometricPieceEquiv` applies the whole-target
`wholeLeviGeometricPieceEquiv` to this permutation and the reversed source
refinement. Its inputs include an arbitrary target refinement `R` of
`C.reverse` and the actual two subgroup equalities used to define this
geometric piece. The source representation is any smooth representation
of the coarse Levi; its carrier universe and the field universe are
independent. Pullback by `leviReverseEquiv C` puts the target action in the
original target coordinates.

The proof first pulls back the whole-target equivalence. The existing
`transportReverseEquiv` converts this pullback to transport by
`C.reversePermutation * reversedPiecePermutation`. Cancellation leaves
`x * b`. The published `transport_mul` expresses this as transport by `b`
followed by transport by `x`. Transporting
`flattenedNormalizedOppositeReverseEquiv` by `x` gives the displayed
equivalence with the original normalized inner opposite Jacquet module
in its flattened coordinates. Every step constructs a representation
equivalence, retaining its actual linear map.

This is derived infrastructure, with no external literature assertion.
No minimality or cuspidality hypothesis is needed for this algebraic
comparison. It makes no minimal-representative, grade-existence,
branch-selection, multiplicity, or continuation claim. Identifying this
permutation with an index of a geometric filtration and proving the
needed subquotient occurrence remain separate obligations.
