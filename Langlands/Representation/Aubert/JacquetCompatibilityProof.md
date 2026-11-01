# Actual reversed-Levi Jacquet compatibility of the Aubert operator

Authors: Worker 165 and Worker 1186.

`Langlands.Aubert.jacquetCompatibility` proves exactly the published
`Langlands.Aubert.JacquetCompatibilityStatement.{uF,uV} F T`, without modifying
that statement or its imported definitions. For every natural rank and actual
ordered positive block shape `B`, it proves the equality of integer-linear maps

```text
Jac_B ∘ D_n
  = transport_(B.reverse -> B) ∘ D_(B.reverse) ∘ Jac_(B.reverse).
```

Every map is the existing map on the full exact finite-length smooth complex
Grothendieck group, whose relations include all actual short exact sequences,
including nonsplit sequences. The field and carrier universes are independent;
the representation carriers are saturated in `Type (max uF uV)`. The prime,
supplied p-adic field, and supplied topology are arbitrary. No admissibility,
irreducibility, cuspidality, finite vector-space dimension, central-character,
preservation, or compatibility premise is added.

This is a derived assembly from the actual geometric lemma, actual functor
comparisons, and the pointwise signed coefficient computation. Its source
assertion and conventions are those documented in the unchanged target
statement pair, namely the reversed-Levi equality of Aubert's Theorem 1.7(2).
The implemented proof uses the following concrete route.

For positive rank, `jacquetAlternatingOperator_positive` in
`Aubert.JacquetCompatibilityAssembly` expands the ambient alternating
induction-Jacquet sum. The published actual geometric lemma is applied to
Jacquet restriction of each induced representation. Its generator formula is
extended to equality of integer-linear maps by exact K0 generator
extensionality, and its finite enumeration is reindexed by the actual minimal
double-coset representatives.

The actual piece-after-restriction comparison in
`Geometric.JacquetPieceGrothendieck` identifies each composite using normalized
Jacquet restriction in stages, the actual flattened-coordinate equivalence,
inverse whole-Levi conjugation transport, and actual refined induction.
The source standard shape for a fixed target refinement and permutation is
unique, by injective conjugation and uniqueness of a standard Levi shape.
Consequently every witness computes the same canonical actual geometric map.

`Geometric.JacquetRegrouping` then regroups these actual maps by the target
refinement while retaining the permutation. Literal target-intersection
equalities and injectivity of flattened Weyl groups identify the fibers.
The published pointwise Jacquet coefficient cancels every permutation except
`B.reversePermutation`. The ambient exponent `n - C.length` becomes exactly
the intrinsic refinement exponent `sum i, (B.size i - (Q i).length)`.
Thus the surviving sum is the actual `jacquetReversalRefinementSum F T B`.

The theorem `jacquetReversalRefinementSum_eq` in this module identifies that
sum. Outer reversal gives an equivalence `outerReverseRefinement B` between
refinements of `B` and `B.reverse`, retaining each inner ordered shape.
Reindexing the finite exponent sum proves
`refinementSignExponent_outerReverse`. For each original refinement `Q`, the
concrete reversed flattened source is
`B.reverse.flatten (outerReverseRefinement B Q)`.
The theorem `conjugatesLevi_outerReverseFlattened` proves its actual
conjugacy to `B.flatten Q` by the same coarse reversal permutation.
`canonicalJacquetGeometricTerm_eq` therefore computes the canonical map using
this explicit witness.

The actual witnessed comparison
`Geometric.jacquetGeometricTerm_outerReverse` identifies that term with reversed
refined induction after reversed refined and coarse Jacquet restriction,
followed by the exact coarse transport in the target statement. Its proof
uses the published flattened-Jacquet comparison for restriction in stages,
the actual inverse-conjugation coordinate identities, and normalized refined
induction under outer reindexing. The last comparison comes from precomposition
on actual covariant smooth induced functions; it preserves the positive
half-modulus covariance and intertwines right translation. Exact K0 generator
extensionality passes that equivalence to all virtual classes. The Jacquet maps
remain the actual upper normalized maps with inverse half-modulus action.

The private finite-sum helper in this module moves the actual integer-linear
transport across the finite sum and changes the refinement index through this
equivalence. Sign preservation and the witnessed term equality discharge all
its hypotheses. Expanding the existing product-Levi Aubert operator then gives
the required transported reversed product-Levi sum. The transport is
`leviTransportK0` for `B.reversePermutation` and the exact concrete witness
`conjugatesLevi_reversePermutation F.Carrier B`; its direction is from
reversed coordinates to original coordinates.

Rank zero is covered by `jacquetCompatibility_rankZero` in the assembly
module. Published actual rank-zero Aubert identities make the ambient and
product-Levi operators identity maps. The empty block shape equals its
reverse, the unique permutation belongs to its block Weyl group, and actual
block-preserving Levi transport is identity on exact K0. This proves the
rank-zero target equality with its actual functors. The final theorem splits
the rank into zero and successor; in positive rank it composes the geometric
expansion with the survivor-sum equality.

No analytic segment classification, multisegment or quotient exhaustion,
ordered-head existence, tempered-block uniqueness, square-integrable or
regular classification/exhaustion, or irreducible-image conclusion enters
this proof. The supporting modules are supplied as exact source pairs when
not yet present in the workspace's published base; pending review is not
used as an assumed mathematical premise.
