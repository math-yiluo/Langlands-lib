# Restriction of real Weil block data to complex block data

This is an internal construction from the published character data,
real Weil actions and block-list operations. The accompanying Lean file defines actual
norm-pulled-back characters and finite lists; it does not assert global compatibility.

The real convention is `sgn(x)^parity * |x|^exponent`. The complex convention is
`(z/‖z‖)^weight * ‖z‖^(2*exponent)`, with Euclidean norm. Pullback along the published
`complexNorm`, `z ↦ z*z̄`, therefore has weight zero and the same exponent. The character
equation is reused from `ComplexCharacterData.trivial.twistReal c`.

`RealCharacterData.complexRestriction` has character `c.character.comp complexNorm`, weight
zero and exponent `c.exponent`; its three projection lemmas are definitional.
`RealBlock.restrictToComplex` sends a character block to `[c.complexRestriction]` and an
induced block to `[d, d.conj]`. Here `conj` is the existing pullback by complex conjugation.
The two block equations and the block length equation follow by reduction and case analysis.

`realParameterRestrictToComplex ds` is `ds.flatMap RealBlock.restrictToComplex`. The empty,
cons and append equations are list identities. Its length is `realRank ds`, proved by list
induction using the block length equation. Permutation preservation uses
`List.Perm.flatMap_right`, retaining repetitions and the two entries of every induced block.

The formulas are motivated by the already published `realCharacter_ofComplex`,
`twoDimensionalAction_restrict`, and `ComplexCharacterData.realInducedRepresentation_ofComplex`:
on the complex Weil subgroup a real character acts by the norm pullback, and an induced
block has the diagonal actions of `d.character` and its conjugate pullback. This module
proves no new isomorphism between actual sum models.

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), registered source `arthur-clozel-1989-base-change`, Chapter III Definition 1.2,
printed p.199 / PDF p.213, and Theorem 5.1, printed pp.212–213 / PDF pp.226–227, motivate
later use at all places. These block operations are an internal formulation, not a verbatim
source assertion. In the later real-place clause, a real upstairs place uses the same real
block list, and a complex upstairs place uses `realParameterRestrictToComplex ds`. Its actual
place subtype is formed with its `IsReal` or `IsComplex` proof; this vocabulary does not
choose a new place coordinate.

No character classification, global parameter existence or uniqueness, induced automorphic
realization, restricted sum-model isomorphism, or compatibility with global base change is
proved here. That compatibility remains an explicitly unproved external premise. The
constructions have no field or spectral-presentation universe.
