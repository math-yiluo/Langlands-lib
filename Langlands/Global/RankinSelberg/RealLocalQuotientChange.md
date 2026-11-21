# Transport of compatible real quotient measure data

This module adapts the quotient transport of
`ComplexLocalEqualQuotientChange` to the real Borel quotient in
`ArchimedeanIntegrals`. It is an internal measure construction for the
additive-character normalization, independent of the rank gap of a consumer.

Let `N` be the upper unitriangular subgroup of `GL_(r+1)(ℝ)`. The parameter
`t` is any matrix whose conjugation preserves `N` in both directions. The
proof of `conjugation_diagonal_mem_iff` supplies this condition for an
invertible diagonal matrix, in particular for the character-changing
power diagonal. It applies diagonal normalization first for the diagonal
and then for its inverse.

`RealCharacterChange.changeQuotientMeasure` takes the three measures (on the
group, the subgroup and the left quotient) to their pushforwards by the
respective conjugation equivalences. The general quotient transport lemma
preserves the Weil compatibility fields simultaneously; the group and
subgroup measures remain Haar, and right invariance of the subgroup measure
is also preserved. In particular it does not equate the original and new
quotient measures or discard a change-of-variables constant.

`shiftQuotient` then composes the conjugation on `N \\ G` with right
translation by `t*z`. On representatives the resulting map sends `g` to
`t*g*z`. Right invariance of the transported quotient measure shows that
this map is measure-preserving from the original to the transported
measure for every `z`, with the same transported data for all `z`.
Neither analytic continuation nor a functional equation is asserted.
