# Finite exceptional sets for completed residue cardinalities

This internal construction supplies the finite-exception arithmetic step
in Conrad, *Weil and Grothendieck approaches to adelic points* (December
31, 2011), Theorem 4.5, printed p.13, last paragraph. It uses all actual
finite places of a number field and all actual discrete curve places of
a function field over a finite constant field. All types share an
arbitrary universe.

For each real number `B`, the constructors
`finitePlaceSmallCompletionResiduePlaces` and
`curvePlaceSmallCompletionResiduePlaces` return the exact finite set of
places where the cardinality of the actual completed residue field is
at most `B`. Their membership lemmas give this equivalence, and their
`_lt` lemmas give the strict lower bound outside the finite set.

The number-field proof uses the published equality between the completed
residue cardinality and the absolute ideal norm, followed by the
published finiteness of bounded absolute norms.

The function-field proof uses the published finite-poles theorem directly.
Given a natural bound `N`, put `m = N! + 1` and let `s` be the image of
the rational-function parameter in the actual field. Every element `x`
of every finite field of cardinality at most `N` satisfies `x^m = x`:
for nonzero `x`, its multiplicative order divides `q - 1`, which divides
`N!`; zero satisfies the same identity. Transcendence of `s` makes
`s^m - s` nonzero. If `s` is integral at a place with residue cardinality
at most `N`, its reduction satisfies that identity, so `s^m - s` is a
nonunit and its inverse is not integral. Thus all such places lie in the
union of the pole sets of `s` and `(s^m - s)⁻¹`, which is finite by the
published theorem. The finiteness of the original residue fields is
also imported from its published proof. The canonical completion-residue
equivalence transfers the bound to completed integer rings; the natural
floor of a real bound reduces it to the natural-number result.

This argument does not require a separating presentation, a separable
extension of the rational function field, or rational-place
classification. The finite constant field supplies perfectness for the
imported finite-poles theorem. It also does not use or prove a Lang–Weil
estimate, any point-surjectivity assertion, spreading, or adelic openness.
