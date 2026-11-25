# Constituents of reordered complex standard modules

`complexStandardOperators` collects right translations by `U(n)` and the
Lie operators along real matrix directions on the compact-finite standard
module. A constituent for those operators is a stable subspace with an
equivariant surjection onto the constituent space. The transfer theorem uses
a fixed nonzero target on which every jointly stable subspace is zero or the
whole space.

For an adjacent swap, `exists_affine_swap` supplies intertwining linear
equivalences at infinitely many shifts of one exponent. The compact action
is fixed on each side of the swap. The original Lie operators are the values
of the two affine families at zero. Compact finiteness, continuity of the
compact matrix coefficients, and admissibility of the source standard
module permit the compact specialization theorem to transfer the constituent
at zero. Induction on the list permutation applies the adjacent result at
any prefix and composes the transfers for successive permutations.

This proves the occurrence comparison for complex standard modules used in
the proof of `CuspidalIsobaricSupportStatement`. The source comparison comes from Badulescu and Renard (2010),
Remark 2.3 on p. 1123 (PDF p. 10) and Proposition 2.4 on p. 1124 (PDF p. 11).
The implemented proof uses affine specialization and the Library's unlinked
swap theorem. Tadić (2009), §3 (author's PDF p. 11), describes the linkage
relation used in the deformation.
