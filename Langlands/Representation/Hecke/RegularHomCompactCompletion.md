# Regular Hecke-module maps and compact-open completion

In Renard, *Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, I.1.4 (printed p. 10, PDF p. 16) identifies the completion of a
module with maps out of the left regular module. The calculation following
VI.9.7 (printed p. 206, PDF p. 212) uses this identification for the Hecke
algebra. The theorem and proof of VI.9.7 (printed p. 205, PDF p. 211) use the
inverse limit over compact-open subgroups. This module compares those
constructions for a smooth complex representation of a Hausdorff locally
compact nonarchimedean group and any left Haar measure.

`heckeAction_normalizedIndicator_eq_compactAverage` identifies the integrated
normalized indicator with `Compact.averageMap`. The integrated operator is
constant on the translates of any vector by the compact subgroup, by right
invariance of the indicator and triviality of the modular character there.
It therefore has the same value on a vector and on its compact average. The
indicator acts as the identity on the averaged vector.

`regularHomCompactCompletionEquiv` is an additive equivalence from
`RegularHeckeHom`, the actual `NonUnitalModuleHom` with the left regular source
and the integrated target action, to `CompactCompletion.completion`. It sends
`q` to the family with component `q(e_K)` at `K`. It restricts the all-idempotent
family from `regularModuleHomLeftLimitComparison` to the normalized indicators
`e_K`. They are cofinal because each idempotent has a normalized compact-open
two-sided unit. To extend a compact-open family `x` to a component at `e`,
apply `e` to `x_K` for any `K` with `e ≤ e_K`. The component at `K ∩ L` proves
independence of choices by the absorption identity `e e_K = e` and the
transition law for `x`. The inverse evaluates at a test `b` as `b · x_K`
whenever `b e_K = b`. Postcomposition by an intertwiner maps each component
by that same intertwiner.

Under the inverse equivalence, translating `x` by `g` gives the map taking
`b` to the value of the original map at the right translate of the Haar
distribution `b` by `g⁻¹`. This right translation includes the Haar modular
factor, as in `Hecke.Homomorphism.rightRepresentation`. The proof chooses a
compact-open right unit for `b` and a right unit for the translated test
inside its conjugate subgroup. Compatibility of completion components and
conjugation of the averages reduce the two evaluations to the modular
right-translation formula for the integrated action.
