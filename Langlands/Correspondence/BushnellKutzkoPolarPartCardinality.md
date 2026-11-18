# Cardinality of the Bushnell–Kutzko polar-part model

The coefficient values of a polar part generate the full finite extension. If a Galois
automorphism fixes every value, its cyclic subgroup fixes the intermediate field they generate,
so the automorphism is the identity. Mathlib's equivalence for free actions then expresses the
polar parts as the product of their orbit set and the Galois group. The degree of the extension
is the order of that group.

At positive level, the support and tower equivalences also identify the polar parts with the
label data times `Fin f`. A point of `Fin f` gives an injection of the label data into the
finite set of polar parts. The two product counts then give the same cardinality after
cancelling the positive factor `f`.

At level zero, a polar part is a generating tuple of length one. Its only degree is `n`
and its coefficient field has exponent one. Evaluation at the unique index identifies the
one-stage towers with the degenerate polynomial labels using the prime-power hypothesis.
The product count then cancels the factor `n`. For both levels, the prime-power hypothesis
identifies `labelFieldSize q` with `q` in the numerical count.

This argument implements the finite-field count in route-note Lemma `lem:BKlabels`.
