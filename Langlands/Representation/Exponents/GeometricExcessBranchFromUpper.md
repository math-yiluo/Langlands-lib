# Strict multiplicity excess selects a noncoarse whole opposite piece, from the upper theorem

This internal conditional derivation proves

```
glGeometricExcessBranch_of_upper (hupper : PadicGeometricLemmaTheorem.{uF, uW}) :
  GLGeometricExcessBranchStatement.{uF, uV, uW}
```

The hypothesis is the published proposition
`Geometric.PadicGeometricLemmaTheorem`, the normalized upper geometric lemma for
every pair of standard Levis of positive-rank `GL` over every finite p-adic
extension. The conclusion is the published proposition
`GLGeometricExcessBranchStatement` of
`Langlands.Representation.Exponents.WeylBranchPiecesStatement`. Its statement
reads: if the composition-series multiplicity of the irreducible cuspidal `ρ`
(pulled back to the refined Levi as `τ`) in the inner opposite Jacquet module
`innerJacquet T B S V` is strictly smaller than in the ambient opposite Jacquet
module `ambientJacquet T B S V`, then some minimal representative
`x ∉ blockWeyl B` from `B` to `B.flatten S` conjugates a whole flattened Levi
`B.flatten S'` onto `B.flatten S`, and `ρ` is an actual subquotient of the
transported inner opposite Jacquet module along `S'`.

The module proves neither `PadicGeometricLemmaTheorem` nor the unconditional
`GLGeometricExcessBranchStatement`. Once the upper theorem is in the Library,
applying `glGeometricExcessBranch_of_upper` to it gives the unconditional
statement.

## Combinatorial lemmas (`GeometricExcessBranch`)

- `index_val_of_eq`: the numerical value of `B.index j a`, computed for a
  block label `j` that is only propositionally equal to `i`. The sum of the
  sizes of the blocks before `i`, plus `a`. It follows from the published
  `LeviAdmissibility.index_val` by substitution.
- `reverse_reverse`: `B.reverse.reverse = B`, from `Fin.rev_rev` on the size
  function.
- `index_rev_rev`: `B.index i.rev.rev a = B.reverse.reverse.index i a`, by
  comparing the two values given by `index_val_of_eq`.
- `reverse_reversePermutation`: the reversal permutation of `B.reverse` is the
  inverse of the reversal permutation of `B`. The proof checks this on the
  standard coordinates `B.reverse.reverse.index i a`, using the published
  `reversePermutation_index` twice and `index_rev_rev`.
- `blockPermOf_mul`, `blockPermOf_one`: blockwise permutations multiply
  blockwise, and the blockwise identity is the identity. Both are checked on
  standard coordinates with `blockPermOf_index`.
- `innerReverse_mul_innerReverse_reverse`: for a refinement `P` of `B`,
  `innerReversePermutation B P * innerReversePermutation B (reverseRefinement B P) = 1`.
  In each block this is `reverse_reversePermutation`.
- `eq_one_of_minimal_mem_blockWeyl`: suppose `x` is a minimal representative
  from `B` to `C`, `x` lies in `blockWeyl B`, and `1` is also a minimal
  representative. Then `x = 1`: the two have the same double coset, and the
  published `weylDoubleCoset_injective` applies.
- `isMinimalRepresentative_one_flatten`: `1` is a minimal representative from
  `B` to `B.flatten S`, by strict monotonicity of standard coordinates.
- `map_leviEmbedding_refinedLevi`: the image of `refinedLevi B S` under
  `B.leviEmbedding` is the standard Levi of `B.flatten S`, from
  `leviEmbedding_mem_flattenedLevi_iff` and `flattenedLeviSubgroup_le`.
- `conjugatesLevi_of_target_full`: take the intersection refinements `P` and
  `Q` of a geometric-lemma label `w` from `B` to `C`. If
  `refinedParabolic C Q = ⊤`, then `w` conjugates the flattened Levi
  `B.flatten P` onto `C`. The proof applies the published
  `conjugatedLevi_eq_refinement_of_source_full` with the roles of `B` and `C`
  exchanged (label `w⁻¹`), rewrites the refined Levi with
  `map_leviEmbedding_refinedLevi`, and inverts the conjugacy with
  `conjugatesLevi_inv`.
- `leviConjugation_reverse`: conjugation by `C.reversePermutation` from
  `C.reverse` to `C`, as a Levi isomorphism, is
  `(leviReverseEquiv C).symm`. Both sides agree after the injective Levi
  embedding, by `leviConjugation_embedding` and `reverseMatrix_mul_leviEmbedding`.

## Reversed representation

`reversedLeviRepresentation C ρ` is the representation `ρ` of `C.Levi`
restricted to `C.reverse.Levi` along `(leviReverseEquiv C).symm`, that is,
with its block labels reversed. `isLeviQuasicuspidal_reverse` shows that
quasicuspidality passes to it. The proof applies the published
`isLeviQuasicuspidal_transport` along the minimal representative
`C.reversePermutation⁻¹` from `C` to `C.reverse`. Minimality comes from
`isMinimalRepresentative_reverse_inv_mul`. The resulting transport is
identified with `reversedLeviRepresentation` by `transport_inv` and
`leviConjugation_reverse`.

## Cuspidal exclusion

`not_isSubquotient_properInduced` restates BZ77 2.4(d), as published in
`CuspidalSupport.padicProperRefinedInduction`, for an irreducible target.
Let `R` be a proper refinement of `C` (`refinedParabolic C R ≠ ⊤`) and let
`σ` be an irreducible quasicuspidal representation of `C.Levi`. Then `σ` is
not a subquotient (in the sense of `IsSubquotient`) of any normalized refined
induction from `R`.

Proof: a subquotient witness gives an invariant subspace `U` and a surjective
intertwiner `q : U → σ`. The kernel of `q` is invariant, so
`D = U / ker q` is a smooth subquotient of the induced representation.
`quotKerEquivOfSurjective` gives an equivalence from `D` to `σ`, so `D` is
quasicuspidal (`isLeviQuasicuspidal_iff_of_equiv`). BZ77 2.4(d) then makes
`D` a subsingleton. This contradicts the nontriviality of the irreducible
`σ` (`QuasicuspidalEmbedding.nontrivial_of_isIrreducible`).

`geometricPieceFunctor_congr` says that equal permutation labels give equal
geometric-piece functors, whatever proofs of the Levi-intersection equations
are supplied.

## Proof of `glGeometricExcessBranch_of_upper`

Fix the data of the statement. Write `A` for the smooth representation `V`,
`C = B.flatten S` for the fine shape, `L = leviReverseEquiv C`,
`E = flattenedLeviEquiv B S`, and
`τ' = reversedLeviRepresentation C ρ` on `C.reverse.Levi`.
`FiniteTensorFiltration.compSymmComp` identifies `τ'` pulled back along `L`,
and `τ` pulled back along `E`, with `ρ` itself.

1. **Upper filtration.** `hupper` at the source `B` and the reversed target
   `C.reverse` gives refinements `P w`, `Q w` and an enumeration `e`. With
   these, the upper Jacquet module of the normalized induction,
   `jacquetInductionFunctor T B C.reverse`, is glued (`IsGluedFrom`) from the
   actual geometric pieces.
2. **Identity piece.** `w0 = reversedPieceMinimalRepresentative B S` at
   `x = 1` labels the piece belonging to the identity. The published
   `chosenRefinementReversedWholeLeviGeometricPieceEquiv` with `x = 1`, and
   `transport_one`, identify that piece, pulled back along `L`, with the inner
   opposite Jacquet module pulled back along `E`. Multiplicity transport along
   group equivalences and representation equivalences
   (`groupEquivJordanHolderMultiplicityTransport`,
   `equivJordanHolderMultiplicityTransport`) turns the hypothesis on
   `innerJacquet` into multiplicity `m_in` of `τ'` in this piece.
3. **Ambient multiplicity.** The published
   `Parabolic.flattenedOppositeJacquetComparison` identifies the composed
   opposite Jacquet module of the normalized induction, pulled back along
   `E`, with its whole opposite Jacquet module along `C`. The published
   `oppositeJacquetReverseEquiv` identifies the upper Jacquet module along
   `C.reverse`, pulled back along `L`, with the same whole opposite Jacquet
   module. The same transport lemmas give multiplicity `m_amb` of `τ'` in
   `jacquetInductionFunctor T B C.reverse` applied to `A`.
4. **Excess selection.** The published
   `IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess` and
   `m_in < m_amb` give an index whose label `w ≠ w0` has a piece containing
   `τ'` as an actual subquotient.
5. **Whole target.** `τ'` is irreducible (`isIrreducible_comp_mulEquiv_iff`)
   and quasicuspidal (`isLeviQuasicuspidal_reverse`). The piece is a
   normalized refined induction from `Q w`, so `not_isSubquotient_properInduced`
   forces `refinedParabolic C.reverse (Q w) = ⊤`. Then
   `conjugatesLevi_of_target_full` gives that `w` conjugates `B.flatten (P w)`
   onto `C.reverse`.
6. **Noncoarse representative.** Put `S' = reverseRefinement B (P w)` and
   `x = reversedPiecePermutation B (P w) C.reverse w`. The published
   `isMinimalRepresentative_reversedPiece` and `conjugatesLevi_reversedPiece`,
   rewritten with `reverse_reverse`, give that `x` is minimal from `B` to `C`
   and conjugates `B.flatten S'` onto `C`. Unfolding
   `reversedPiecePermutation` and using `reverse_reversePermutation` and
   `innerReverse_mul_innerReverse_reverse` shows
   `reversedPiecePermutation B S' C x = w`. By `geometricPieceFunctor_congr`,
   the subquotient from step 4 is a subquotient of the piece at this label.
   Pulled back along `L`, it is a subquotient of `ρ`. The equivalence
   `chosenRefinementReversedWholeLeviGeometricPieceEquiv` (at `S'`, `x`)
   identifies that piece with the transported inner opposite Jacquet module
   along `S'`, which gives the required subquotient.
7. **`x ∉ blockWeyl B`.** If `x ∈ blockWeyl B`, then
   `eq_one_of_minimal_mem_blockWeyl` gives `x = 1`. Then
   `sourceLevi_eq_refined_of_flattened_conjugates` at `x` and at `1` make the
   refined Levis of `S'` and `S` equal, so `S' = S` by
   `blockRefinement_eq_of_refinedLevi_eq`. Hence
   `w = reversedPiecePermutation B S C 1 = w0`, contradicting step 4.

## Provenance

The overall argument follows the standard Bernstein–Zelevinsky reasoning: in
the geometric-lemma filtration, a cuspidal constituent can only appear in a
piece whose inducing parabolic is whole (BZ77 2.4(d), with 2.12 for the
geometric lemma). Here a strict multiplicity excess over the identity piece
forces such a piece with a label other than the identity. The Lean derivation
is internal. Its inputs are the published lemmas named above: the upper
geometric lemma as an explicit hypothesis, BZ77 2.4(d) as
`padicProperRefinedInduction`, the reversal and transport equivalences of
`Geometric.RefinedOppositePieceTransport`, Jordan–Hölder multiplicity
transport, and the excess helper of
`Langlands.Representation.Exponents.WeylBranchMultiplicityExtraction`. It
asserts no further external result.
