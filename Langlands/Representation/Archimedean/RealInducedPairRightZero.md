# Filtration with a zero-weight right induction block

Lean module:
`Langlands.Representation.Archimedean.RealInducedPairRightZero`.

## Statement

`RealInducedPairRightZeroFiltrationStatement` says that for every ambient rank
`n`, lists `pre` and `post`, and complex character data `d` and `e`, the
conditions

- `e.weight = 0`,
- `realRank (pre ++ induced d :: induced e :: post) = n`, and
- `realBlockExponent (induced d) < realBlockExponent (induced e)`

imply `RealAdjacentFiltration n pre post (induced d) (induced e)`.
The left weight, linking, parity and exponent gap have no further restrictions.
The theorem `realInducedPairRightZeroFiltration` proves this proposition using
`RealInducedPairRightZero.filtration`.

## Proof

First obtain `RealInducedCharacterFiltrationStatement` from
`RealInducedCharacter.realInducedCharacterFiltration_of_landing`. Supply its
induced-first landing input by `RealSwapLandingIntegral.inducedFirst` and its
character-first input by
`RealSwapLandingMirror.characterFirst_of_inducedFirst` applied to the same
theorem. Thus the local induced-character theorem has no remaining premise.
The five helper modules `RealInducedCharacterMaps`, `RealInducedCharacterLanding`,
`RealInducedCharacterPushforward`, `RealInducedCharacterHard` and
`RealInducedCharacterFiltration` contain its construction; their paired
Markdown explains its maps, landing, uncertainty argument and case analysis.

Apply `RealInducedInducedNonzeroReduction.right_zero` with this closed theorem.
That proved reduction expands the zero-weight block `e` into the characters
`first e` and `second e`, of parities `1` and `0`, both with exponent
`e.exponent`. It applies the induced-character filtration first to
`(induced d, character (first e))`, with the second character in the suffix,
then to `(induced d, character (second e))`, with the first character in the
prefix. Induction in stages supplies the arbitrary ambient rank and
surrounding lists. `RealInducedPairWeightZero.fuse_right` combines these
filtrations and identifies the expanded standard modules with the original
ones. The construction retains the admissible pieces, intertwining modulo
earlier ranges, and spanning required by the actual adjacent filtration.

## Provenance and scope

This is an internal consequence of proved constructions in the Library.
The five induced-character helper pairs are reused unchanged from the work
of Workers 763 and 764; the landing theorems, uncertainty theorem used inside
the hard case, and zero-weight reduction are proved inputs. No additional
literature claim, supplied intertwiner or classification premise is assumed.

This supporting result covers every zero-right-weight case, including linked
pairs and pairs with both weights zero. It retains `e.weight = 0` and does not
prove the unrestricted `RealInducedInducedFiltrationStatement`.
