# Separation of the end weights by the actual Tits positive cocharacter

Author: Worker 239.

This internal consequence of `TitsIndexData.compatible` applies to any field,
actual Tits index `d`, numbering of its simple vertices by `Fin n`, and family
of characters `χ` of its maximal split torus whose adjacent differences are
the actual numbered simple-root restrictions. It does not assume a matrix
presentation or prove its existence.

`weightValues` evaluates the supplied characters on `d.positiveCocharacter`.
Every simple-root restriction has nonnegative value: zero restrictions have
value zero, while `d.compatible` and positivity of a simple root give positive
value for a nonzero restriction. In particular a distinguished vertex gives
a positive value, since distinguished means that its restriction is nonzero.
`weightValues_sub` identifies adjacent differences with these root values,
and `weightValues_antitone` proves that the resulting finite sequence is
nonincreasing.

For `n > 0`, a distinguished first vertex makes the first adjacent difference
strictly positive, so every later weight has strictly smaller value than the
first. A distinguished last vertex similarly makes the last weight strictly
smaller than every earlier weight. `first_weight_ne` and `last_weight_ne`
then give the corresponding inequalities of characters. These arguments use
the actual positive cocharacter and require no assumption on characteristic,
Cartan pairings, or the star action.

The derivation supplies the weight-separation step for outer type A matrix
descent. It asserts no preservation of coordinate lines by a matrix and no
Hermitian presentation; those require additional matrix and descent arguments.
