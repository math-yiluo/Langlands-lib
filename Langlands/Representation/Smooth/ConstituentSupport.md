# Actual irreducible constituent support from exact classes

This internal algebraic module works with smooth representations over an arbitrary
field, with independent coefficient, group and carrier universes. Its
`HasConstituentSupportIn A B` is the proposition that every actual irreducible
smooth subquotient of `A` is an actual subquotient of `B`, in the same carrier
universe. It does not assert that `A` itself is a subquotient of `B`.

`hasFiniteLength_of_isSubquotient` uses the actual injective/surjective
presentation of a smooth subquotient. Finite length as a module over the group
algebra passes first through the injection and then through the surjection.

`compositionMultiplicity_pos_iff_isSubquotient` identifies positive natural
composition multiplicity with existence of an actual irreducible subquotient.
For the forward implication, a positive finite cardinal supplies a factor in
the chosen actual composition series and an intertwining equivalence with the
given irreducible object. That factor is a quotient of the corresponding actual
subrepresentation. Conversely, the published `simpleSubquotientFactor` theorem
identifies an irreducible actual subquotient with a factor of that series, giving
a positive finite cardinal. This uses the existing composition-series and exact
Grothendieck-group constructions; no support-existence or classification theorem
is assumed.

`exists_irreducible_subquotient` extracts a simple factor from an actual finite
composition series of a nonzero object. If the series had no factors, the
published zero-filtration result would make its carrier subsingleton,
contradicting nontriviality. A factor of the resulting nonempty finite index set
is the required actual smooth subquotient, in the original carrier universe.

`hasConstituentSupportIn_of_class_natural_multiple` proves that an identity
`[A] = N • [B]`, with `N` natural, in the full exact finite-length Grothendieck
group implies `HasConstituentSupportIn A B`. Apply the published `factorMap` to
the identity and evaluate at the irreducible isomorphism class of an actual
irreducible subquotient `D` of `A`. Its coordinate on `A` is a positive natural
number. If `D` were absent from `B`, its coordinate there would be zero, forcing
the positive coordinate on `A` to be zero in the integers, a contradiction.
The conclusion also holds when `N = 0`; the hypothesis then precludes any such
constituent of `A`.

`hasConstituentSupportIn_of_class_sum` proves the analogous result when `[A]`
is a finite sum of classes `[M i]` and every `M i` has constituent support in
`B`. An absent constituent of `B` has zero multiplicity in every summand,
and evaluation of the class identity gives the same contradiction.

The provenance is internal: the proof combines the published actual
subquotient presentation, `simpleSubquotientFactor`, zero-filtration theorem,
and the comparison of the exact group with irreducible composition factors.
Every actual short exact relation, including nonsplit ones, remains in the
existing Grothendieck quotient. These results do not replace actual support
filtrations, assert splitting of representations, or prove Aubert concentration
or signed effectivity.
