# Exact normal kernels from inverse positive multiple characters

This internal module constructs an actual finite matrix representation with
a prescribed normal subgroup as its full scheme-theoretic kernel, subject to
an explicit inverse positive multiple character occurrence hypothesis.
The base is an arbitrary field; no smoothness, reducedness or algebraic
closedness is assumed.

`nonempty_kernelRepresentation_of_inverse_multiple` starts with an ambient
representation, a normalized vector of subgroup character `χ`, and the
assumption that every test point preserving its line lies in the subgroup.
Its additional input is a nonzero vector in another ambient representation
of character `-((r + 1) • χ)`, for some natural number `r`.
The proof normalizes a nonzero coordinate of that vector to one. The positive
tensor power of the first vector has character `(r + 1) • χ`; tensoring the two
vectors cancels the characters. The published normal fixed subrepresentation
construction gives an exact kernel: fixing this tensor preserves the positive
tensor power line, hence the original line, on every scheme test.

`InverseMultipleNormalCharacterVector` packages a positive exponent, an actual
ambient representation and a nonzero vector of the inverse multiple character.
`HasInverseMultipleNormalCharacters i` is the Prop-valued occurrence condition
for every occurring character in every ambient representation of positive
dimension indexed by `Fin`. It does not assert its own truth.

`nonempty_kernelRepresentation_of_normal_closed_inverse_multiples` applies
Chevalley's published line stabilizer theorem to a closed normal subgroup of
an affine locally finite-type group. The coordinate line determines a subgroup
character. The explicit occurrence hypothesis supplies the inverse multiple
vector, and the previous construction gives the exact kernel.
`normalKernelRepresentationOfInverseMultiples` chooses this representation.
The kernel equality is an equality of subgroup functors on all scheme tests.

The provenance is the proof route of Milne, *Algebraic Groups* (2017),
Corollary 4.29 (printed p. 95, PDF p. 111) and Lemma 5.17 (printed p. 103,
PDF p. 119), using the inverse multiple character conclusion of Lemma 5.16.
The official erratum to Corollary 4.29 replaces the tensor target `W` by `V'`;
here both tensor factors are actual ambient representations. The coordinate
normalization and package interfaces are internal choices. This module leaves
the occurrence hypothesis explicit and proves no general inverse multiple
occurrence or quotient existence theorem.
