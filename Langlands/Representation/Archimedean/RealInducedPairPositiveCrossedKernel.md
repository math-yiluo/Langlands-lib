# The actual kernel remaining in the positive crossed quotient

This internal construction refines the actual positive-inner crossed quotient.
It applies to every linked pair with positive original absolute weights and
positive signed inner weight `H`, using the same endpoint parities as
`RealInducedPairCrossedMiddleQuotient`. No further squared-weight bound is used.

Write `A:X→V` for the original surjective four-character presentation,
`B:X→J` for the actual middle tail, `s:J→X` for its explicit right inverse,
`U:J→C` for the mixed crossed quotient and `q:V→C` for the positive crossed
quotient. The existing factorization is `q A=U B`. The elementary split-map
lemma gives

`ker q = A(ker B) + (A s)(ker U)`.

For the forward containment, lift a kernel vector to `x` in `X` and write
`x=(x-s(Bx))+s(Bx)`. The first summand is in `ker B`, and `Bx` is in
`ker U`. The reverse containment follows directly from the factorization
and `B s=id`. All terms are actual linear-map images in the target module.

The rank-one binomial/tail kernel equality identifies `ker B` with the
last inner binomial image. Its image under `A` is `range prefixMap`.
The incoming four-crossing word realizes that range as
`range qW + range qR`, where `qW` is the actual exchanged-pair map and
`qR` comes from the outer mixed source. The generic middle crossings are
surjective, so the outer rank-one decomposition gives equality of these
ranges. The exchanged map intertwines exactly; the outer-source map
intertwines modulo the exchanged range.

The outer source preserves exponent support and has weight-square sum
`P²`. Since `P=L+M+H` and `H>0`, it is an allowed strictly heavier source.
The actual `middleSection=A s` intertwines modulo the displayed prefix,
and its range together with that prefix spans `V`. It also satisfies
`q middleSection=U`.

The construction uses the explicit right inverse of the middle tail and the
surjectivity and exact factorization of the original presentation. It does
not assume a classification theorem or a range identity.

`RealInducedPairPositiveCrossedKernelStatement` packages these maps,
intertwining properties, the kernel decomposition, the exact mixed
factorization and the spanning equality.
`realInducedPairPositiveCrossedKernel` proves the statement.
The helper `ker_eq_prefix_iff` makes the remaining obligation precise:
`ker q=range prefixMap` if and only if
`middleSection(ker U)≤range prefixMap`.

The remaining summand has not been absorbed into the allowed earlier source
images. This module neither asserts that containment nor proves the
unrestricted `RealInducedInducedFiltrationStatement`.
