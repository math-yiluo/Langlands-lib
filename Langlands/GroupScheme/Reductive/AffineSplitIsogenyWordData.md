# Compatible descending simple words for a root-datum isogeny

This internal construction completes the simple-word transport used in
`AffineSplitIsogenyWeylMap`. It takes corresponding bases and positive
systems as explicit inputs. No group-scheme existence assertion is made.

`targetSimpleWords` is a complete family of target simple words. At a
target root it uses the source word at the corresponding source root,
then applies the inverse root bijection to its initial simple root and
every letter. Reflection compatibility proves the final-root identity.
Its Weyl family is definitionally the previously constructed
`targetWordFamily`.

The transpose equation, evaluated on roots and coroots, relates the two
Cartan pairings by positive root factors. Thus the two pairings have the
same sign. This proves that descending source words give descending target
words when both the supports of the bases and their positive systems
correspond. The three descending-word clauses transfer separately:
simple roots retain the empty word; a positive nonsimple root retains a
reflection with positive pairing; and a negative root retains the word
of its opposite followed by the chosen simple root.

The construction does not claim that the two height functions are equal.
It proves the exact published `IsDescendingWords` predicate. It supplies
compatible combinatorial data for the normalized root calculations, while
normalization and the rank-two relation comparisons remain separate
obligations.
