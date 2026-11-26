# The evaluation comparison for the Hermitian contragredient

`Langlands.Renard.CompactRepresentation.conjugateContragredient` proves
[`ConjugateContragredientStatement`](ConjugateContragredientStatement.md).
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, IV.2.1, opening paragraph, printed p. 96
(PDF p. 102). Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

An equivariant conjugate-linear equivalence \(T\) from one coefficient
representation to another sends smooth linear functionals by
\(\ell\mapsto (y\mapsto\overline{\ell(T^{-1}y)})\). The two conjugations
make the image functional linear in \(y\). As a map of smooth duals
the formula is conjugate-linear in \(\ell\). Equivariance of \(T\) means
that an open subgroup fixing the original functional also fixes its image.
Applying the same formula with \(T^{-1}\) gives the inverse by involutivity
of complex conjugation.

Apply this construction to the conjugate-linear identity
`ConjSpace.equiv V`. Precomposing with the inverse of the conjugate-linear
identity on the source dual makes the comparison complex-linear. The dual
action uses the inverse group element, so its equivariance follows by
commuting \(T^{-1}\) with that element's action. Evaluation at \(T x\)
then gives \(\overline{\ell(x)}\).
