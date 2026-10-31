# Fixed whole-Levi geometric-piece lifting

`Langlands.glGeometricPieceLifting.{uF,uV}` proves exactly the published
proposition `Langlands.GLGeometricPieceLiftingStatement.{uF,uV}` from
`Langlands.Representation.Exponents.WeylBranchPiecesStatement`. Its type has
no extra premise, and the field universe `uF` and representation universe
`uV` stay independent.

The statement covers every prime `p`, actual p-adic field `F` with a supplied
compatible topology `T`, positive rank `n`, block shapes `B` and `C`,
refinement `S` of `B`, minimal representative `x` from `B` to `C`, witness
`hx` that `x` conjugates the flattened Levi of `S` onto `C`, and smooth
complex representation `V` of `B.Levi`. For these data, the transport by `x`
and `hx` of the inner normalized opposite Jacquet module of `V` along `S`
(read on the flattened Levi) is a subquotient of the normalized opposite
Jacquet module along `C` of the normalized induction of `V`.

## Proof

The proof is one application. The published conditional derivation
`Langlands.glGeometricPieceLifting_of_upper` (module
`Langlands.Representation.Exponents.WeylBranchPieceLiftingFromUpper`) turns
`PadicGeometricLemmaTheorem.{uF,uV}` into the target at the same universes.
The published theorem `Langlands.Geometric.padicGeometricLemma.{uF,uV}`
(module `Langlands.Representation.Geometric.GeometricLemmaProof`) proves
`PadicGeometricLemmaTheorem.{uF,uV}` without a premise. This is the
normalized geometric lemma of Bernstein and Zelevinsky (1977, Theorem 2.12
with Lemma 2.11 and §§5–6) for actual p-adic general linear groups.

Inside the derivation, the upper geometric lemma is applied at source shape
`B` and reversed target shape `C.reverse`. The steps are:

1. `reversedPieceMinimalRepresentative` gives the index of the matching
   piece in the upper filtration.
2. `IsGluedFrom.isSubquotient_piece` shows that this piece is a subquotient
   of the upper Jacquet module of the normalized induction.
3. Restriction along `leviReverseEquiv C` preserves the subquotient.
4. `oppositeJacquetReverseEquiv` identifies the ambient representation with
   the opposite Jacquet module along `C`.
5. `chosenRefinementReversedWholeLeviGeometricPieceEquiv` identifies the
   piece with the transport, by the given `x` and `hx`, of the inner opposite
   Jacquet module along `S`.

The proof does not use irreducibility or cuspidality of `V`. This module
proves no multiplicity-excess, noncoarse-branch or supported-obstruction
statement.
