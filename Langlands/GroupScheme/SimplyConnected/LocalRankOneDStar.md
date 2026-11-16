# The local type-D spin model with automatic nonfork fixation

This internal unit combines the actual full star action on a numbered type-D
diagram with the local quaternionic presentation and exact marking theorem.
Every field and residue characteristic, including characteristic two, is
retained at arbitrary universe.

`localRankOneTypeD_presentation_and_marking_of_five_le` applies to a simply
connected absolutely almost-simple group over a nonarchimedean local field,
with split rank one and a supplied actual `D_n` Cartan numbering, `n ≥ 5`.
It proves existence of the actual quaternionic spin presentation in `n`
variables and proves that the entire distinguished set consists exactly
of the vertex with zero-based number `1`. It requires no supplied condition
on the full star action.

`localRankOneTypeDPresentationOfFiveLe` chooses this proved presentation.
Its type is the existing `LocalRankOneTypeDPresentation K G n`: an actual
central division algebra of ground-field dimension four, a first-kind
involution with symmetric dimension three, a nondegenerate quotient-valued
quadratic form of Witt index one, and an actual morphism from the given
group satisfying `IsSpinCover`.

The proof obtains nonfork fixation from `star_fixes_nonfork_of_D` and applies
`localRankOneTypeD_presentation_and_marking`. The bundled
`TypeDRankOneOrbit` unit also determines the complete full-star image in these
ranks: it is trivial, or, when nontrivial, it is exactly identity and the
fork-tip transposition.

Two exact-index consequences record the cases once the appropriate
star-action hypotheses are available.
`hasRankOneInnerD5Index_of_type_D_five` gives the published inner-D5 predicate
under triviality of the full action.
`hasRankOneOuterD4Index_of_fixes_nonfork` gives the published outer-D4
predicate under explicit nonfork fixation and nontriviality of the full
action. Its exact two-permutation image uses the same original numbering
and interchanges its zero-based vertices `2` and `3`.

This unit supplies no upper bound on `n`, does not decide which star
alternative occurs locally, and does not exclude trialitarian rank-four
actions. It is an intermediate result for the enumeration, rather than a
proof of the full `LocalRankOneTitsIndexStatement`.
