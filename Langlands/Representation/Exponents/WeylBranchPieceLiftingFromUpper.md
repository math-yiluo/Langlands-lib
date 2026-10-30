# Fixed whole opposite-piece occurrence from the upper theorem

This internal conditional derivation applies the actual upper geometric
lemma at source shape `B` and reversed target shape `C.reverse`. Its input
`x` is a minimal representative from `B` to `C` that conjugates the actual
flattened Levi of the supplied refinement `S` onto `C`. The input
representation is any smooth complex representation of `B.Levi`; no
irreducibility or cuspidality is assumed.

The published `reversedPieceMinimalRepresentative` gives the index of
the corresponding piece in the upper filtration. The proof chooses this
index using the finite enumeration returned by the upper theorem.
`IsGluedFrom.isSubquotient_piece` then exhibits its actual functor value
as a quotient of a subrepresentation of the upper Jacquet module of the
normalized induction.

Restriction along `leviReverseEquiv C` preserves this subquotient. The
published `oppositeJacquetReverseEquiv` identifies the ambient
representation with the original normalized opposite Jacquet module.
`chosenRefinementReversedWholeLeviGeometricPieceEquiv` identifies the
target with transport by the same supplied `x` and the same conjugacy
witness `hx` of the original inner normalized opposite Jacquet module,
in flattened coordinates. The geometric lemma's chosen source
refinement is reconciled by that equivalence rather than imposed as an
extra premise.

`wholeOppositePieceSubquotientWitness` returns actual data: a
subrepresentation of the opposite Jacquet module and a surjective
intertwining map from it onto the fixed transported inner module. It
chooses these data from the proved existential; it does not assume a
subquotient or a filtration as an additional input. Its explicit
`GeometricLemmaTheorem T B C.reverse` input is still required.

`glGeometricPieceLifting_of_upper` packages the construction at all
positive ranks and both independent universes. It remains conditional on
`PadicGeometricLemmaTheorem`: this draft does not prove that theorem or
the closed `GLGeometricPieceLiftingStatement`. It also does not prove
multiplicity excess, a noncoarse branch, localization, continuation or
the supported obstruction theorem. The derivation's provenance is the
published filtration subquotient laws and actual reversal and transport
equivalences named above; it asserts no additional external source
result.
