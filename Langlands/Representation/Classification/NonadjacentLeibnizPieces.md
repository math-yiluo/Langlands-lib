# The two-block derivative pieces from the Leibniz filtration

Author: Worker 745. Helper module of the proof of Ze80 Proposition 1.11(a),
first conjunct (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`).

## Results

- `twoBlockDerivativePieces_of_leibniz hL hSD : TwoBlockDerivativePieces F T`
  derives the intermediate proposition of `NonadjacentTwoBlock` from two
  hypotheses: `hL : Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement F T`,
  the published all-rank Leibniz filtration statement (BZ77 4.14(c)), and
  `hSD : SupercuspidalDerivatives F T`, the published BZ77 4.4 statement.
- `nonadjacent_of_leibniz hE hPL hHP hL hSD` proves the target
  `TwoSupercuspidalNonadjacentProductIrreducible F T` by combining the theorem
  above with `nonadjacent_of_twoBlockDerivativePieces`.
- `nonadjacent_of_exactness_leibniz hE hL hSD` supplies `hPL` and `hHP` by
  the published proofs `Mirabolic.derivativeDetection` (module
  `Derivative/MirabolicDerivativeVanishing`) and
  `mirabolicHighestDerivativePairing` (module
  `Derivative/MirabolicHighestDerivativePairingProof`).
- `nonadjacent_of_exactness_leibnizFiltration hE hL` also supplies `hSD`, by
  the published proof `supercuspidalDerivatives` (module
  `Classification/SupercuspidalDerivativesProof`).
- `nonadjacent_of_leibnizFiltration hL` also supplies `hE`, by the published
  proof `Derivative.generalLinearDerivativeExactness` (module
  `Derivative/GeneralLinearDerivativeExactnessProof`), used at carrier
  universe `max uF uV`, the universe of the product representations. Its only
  hypothesis is the Leibniz filtration statement, which the final module
  `TwoSupercuspidalNonadjacentIrreducibilityProof` supplies with its published
  proof.

The chain is split into these steps so that each lemma names exactly which
statements it still takes as hypotheses.

## Proof

`SupercuspidalDerivativePattern ψ A` means that every derivative of `A` of
order strictly between `0` and the rank is zero and that the top derivative is
one-dimensional. `supercuspidalDerivativePattern` gets it for every
supercuspidal `ρ` of positive rank from `hSD`. The rank is first written as
`n + 1`.

Write `a, b` for the factor ranks, `A, B` for the factors and `0 < d < a + b`
for the order. `leibnizPiece_cases` sorts the Leibniz piece at a feasible
index `(i, j)`, `i + j = d`:

- if `0 < i < a` or `0 < j < b`, one factor of `D_i A × D_j B` is zero, so the
  rank-cast product is zero (`subsingleton_rankCast_product`);
- otherwise `(i, j)` is `(0, b)` or `(a, 0)`, because `(0, 0)` and `(a, b)`
  give `d = 0` and `d = a + b`. At `(0, b)`, `D_0 A` is `A` by definition and
  `D_b B` is a one-dimensional representation of `GL_0`, so the piece is
  equivalent to the rank cast of `A` (`nonempty_equiv_rankCast_product_right`).
  At `(a, 0)` the piece is equivalent to the rank cast of `B`
  (`nonempty_equiv_rankCast_product_left`).

`exists_filtration_binary` takes the filtration given by the published
extractor `GeneralLinearDerivativeLeibnizFiltrationStatement.filtration`,
evaluates it at `(A, B)` with `CuspidalSupport.objectFiltrationAt`, and moves
each case along the graded isomorphism. The enumeration of the feasible
indices is arbitrary; only the fact that every graded piece is the piece at
some feasible index is used.

At the top order `d = a + b` the only feasible index is `(a, b)`
(`card_leibnizIndices_top`, from the published `leibnizIndices_top`). So the
filtration has length one, and its only graded piece is linearly equivalent
to the whole derivative (`nonempty_linearEquiv_graded_of_length_one`, which
uses the zero bottom step and the full top step). That piece is the product of
two one-dimensional representations of `GL_0`, so it is one-dimensional
(`finrank_rankCast_product_of_zero_zero`). This gives `finrank_top_binary`.

`restrictedDerivative_twoBlockProduct` shows that the restricted derivative of
`twoBlockProduct ρ ρ'` (rank written `k + l + 1`) equals the actual derivative
of the binary product `T.binaryNormalizedProductFunctor k (l + 1)` at
`(ρ, ρ')`. It rewrites with `binaryNormalizedProductFunctor_obj_eq_twoBlocks`
and uses `generalLinearDerivative_obj_eq_restriction` from
`TwoSupercuspidalDerivativeBridge`. The final theorem rewrites the two
conjuncts of `TwoBlockDerivativePieces` with this equation and applies the
binary results with `a = k`, `b = l + 1`. In the top case the order is passed
as a variable `d` with `d = a + b`, so that Lean does not have to compare
derivatives of orders `k + l + 1` and `k + (l + 1)` definitionally.

## Provenance and dependency audit

All proofs here are original to this module. Published imports:
`Classification/TwoSupercuspidalBinaryProductBridge` (my published helper
module), `Derivative/MirabolicDerivativeVanishing` and
`Derivative/MirabolicHighestDerivativePairingProof` (proofs of detection and
BZ77 3.8), `Classification/SupercuspidalDerivativesProof` (proof of BZ77 4.4),
`Derivative/GeneralLinearDerivativeExactnessProof` (proof of derivative
exactness), `Derivative/GeneralLinearDerivativeLeibnizFiltrationStatement`
(statement module) and `CuspidalSupport/JacquetVanishingHelpers` (for
`CuspidalSupport.objectFiltrationAt`). Helper imports of this proof:
`NonadjacentTwoBlock` and `TwoSupercuspidalDerivativeBridge`. The audit of the
whole closure against the independence list of task `3c9849a4` is in
`TwoSupercuspidalNonadjacentIrreducibilityProof.md`.
