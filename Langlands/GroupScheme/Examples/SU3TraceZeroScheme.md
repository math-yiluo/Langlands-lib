# The represented quadratic trace-zero group

For a separable quadratic field extension `L/k` and a chosen nonzero trace-zero
scalar `η`, this module represents the actual functor sending a commutative
`k`-algebra `R` to the additive subgroup of `R ⊗[k] L` satisfying
`x + conjugation(x) = 0`. Its maps are the actual tensor coefficient maps.

The previously derived equivalence `r ↦ r ⊗ η` identifies this functor with
the one-coordinate vector functor. Evaluation of the sole polynomial variable
therefore corepresents it by the polynomial line. `Corepresented.groupScheme`
equips its spectrum with the group structure determined by this functor.
`traceZeroPointsEquiv` recovers the trace kernel on relative global sections
for every test scheme, and its naturality uses the actual pullback of sections.
The inverse scalar coordinate is natural under arbitrary coefficient change.
Consequently `traceZeroVectorCoordinates` supplies natural coordinates on all
test schemes and `traceZeroVectorIso` is an actual group-scheme isomorphism
with the additive line. The final identity records its coordinate action.
No affineness, reducedness or characteristic hypothesis is placed on test
algebras or test schemes.

This is an internal representability derivation of the multiplication-by-`η`
isomorphism used in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Section C.3, printed page 698 (PDF page 729). The proof uses the explicit basis
and tensor trace calculation in `SU3TraceZeroCoordinates`, followed by the
relative Spec adjunction and the all-test natural-coordinate construction.
Integral depth models and comparison with a supplied relative root group or
apartment filtration are separate obligations.
