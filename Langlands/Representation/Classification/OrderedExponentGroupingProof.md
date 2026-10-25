# Proof of finite weighted equal-exponent grouping

Authors: Worker 175 (proof); Worker 385 (publication preparation and documentation).

`Langlands.Classification.orderedExponentGrouping` proves exactly
`Langlands.Classification.OrderedExponentGrouping`, imported from
`Langlands.Representation.Classification.OrderedExponentGroupingStatement`.
The closing theorem has no additional parameters or hypotheses. It applies to
every natural total rank, positive ordered block shape, and antitone real
exponent function, including the empty shape at rank zero.

The provenance is internal finite combinatorics. Worker 175 isolated this
bookkeeping for the equal-exponent grouping used by
`SquareIntegrableEqualExponentGrouping` in
`Langlands.Representation.Classification.TemperedBlockStatement`. This proof
establishes the finite grouping and coordinate data; it has no analytic or
representation-theoretic induction conclusion. The Lean source reuses
Worker 175's complete proof from revision 5 of the parent task
`ff269d17-8fd7-4bd5-9a5e-6b5107b63f37`.

The private lemma `weightedGrouping` first handles an arbitrary monotone
surjection `q : Fin B.length → Fin m`. For each `j`, it defines the full fiber
`{i // q i = j}` and enumerates it by the increasing order isomorphism
`Fintype.orderIsoFinOfCardEq`. The new shape `D` has length `m` and size
`∑ i : Fiber j, B.size i.val` at `j`. Surjectivity supplies a member of every
fiber, so each such sum is positive. Reindexing the double sum by
`Equiv.sigmaFiberEquiv q` proves that the new sizes sum to the original total
rank. The inner shape `S j` lists the old sizes in the fiber's increasing
order. The enumeration supplies the entire fiber equivalence, its strict
monotonicity, and the size equalities, which are reflexive for these choices.

For the coordinate condition, the proof defines `φ` from the block coordinates
of `D` to `Fin n`. It first resolves the inner coordinate using
`(S j).indexEquiv.symm`, then uses the fiber enumeration and the original
inclusion `B.index`. The published `BlockShape.index_lt_iff`, imported through
`Langlands.Representation.CuspidalSupport.MinimalJacquetProof`, compares
standard coordinates lexicographically. For different outer blocks,
monotonicity of `q` forces the enumerated old blocks into the same order.
Within one fiber, its increasing enumeration orders the old blocks, and
coordinates in a single old block keep their order. Thus
`φ ∘ D.indexEquiv.symm` is a strictly increasing self-map of `Fin n`.
`StrictMono.apply_le` and `StrictMono.le_apply` make this map the identity.
Evaluating that identity at a nested coordinate proves precisely

```lean
D.index j ((S j).index k x) =
  B.index (e j k).val (Fin.cast (h j k) x)
```

with the statement's cast direction.

The closing proof views the exponent function in `OrderDual ℝ` and increasingly
enumerates its finite range. The enumeration gives strictly antitone grouped
real exponents. Its inverse composed with `Set.rangeFactorization` gives `q`;
antitonicity of the original exponents makes `q` monotone, and range
factorization makes it surjective. The order-isomorphism inverse law proves
exponent preservation. Applying `weightedGrouping` and transporting its length
equality supplies all remaining data. None of these constructions requires
positive total rank: when the original shape is empty, its exponent range and
the new shape are empty, and the same argument applies.
