# Pointwise conjugation of compact induced functions

`Langlands.Renard.CompactRepresentation.compactInductionConjugate` proves
[`CompactInductionConjugateStatement`](CompactInductionConjugateStatement.md)
with independent group and coefficient universes.

The comparison appears in David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, IV.2.1, in the
paragraph after Remark 2 and before (IV.2.1.1), printed p. 97 (PDF p. 103).
The registered source is `renard-2026-representations-groupes-reductifs-padiques`
with SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The conjugate-linear identity `ConjSpace.equiv V` intertwines the
coefficient actions by `ConjSpace.rep_apply`. The proof uses
`Induction.smoothFunctionsConjEquiv` to apply this identity pointwise. It
preserves left covariance and the open right stabilizer of each function,
and its inverse applies the inverse coefficient identity pointwise.

By `Induction.isClosed_quotientSupport`, the projected nonzero support of
each smooth induced function is closed. It is compact because
\(H\backslash G\) is compact.
Both directions of the smooth comparison therefore give compact induced
functions. The inverse laws, additivity and conjugate-linearity follow on
the underlying smooth functions.

Precomposing with the inverse of `ConjSpace.equiv` on the compact induced
space makes the comparison complex-linear. The proof checks equivariance
by evaluating at each \(x\), where right translation by \(g\) replaces
\(x\) by \(xg\) on both sides. Evaluating the comparison on the conjugate
of \(f\) thus gives `ConjSpace.equiv V` applied to \(f(x)\).
