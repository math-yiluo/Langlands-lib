# Quotients by centralizers and normalizers of multiplicative-type subgroups

`relativeMultiplicativeTypeQuotient` proves the unchanged published
`Langlands.GroupScheme.RelativeMultiplicativeTypeQuotientStatement.{u}` for
every universe `u`, without additional hypotheses. The base scheme is
arbitrary. The ambient group is smooth and relatively affine, and the
subgroup is closed and of multiplicative type; it need not be a torus or
smooth. The quotient conclusions apply to every supplied centralizer and
normalizer representative.

The proof assembles the following constructions.

1. The multiplicative-type normalizer representability theorem supplies a
   closed subgroup representing the full normalizer.
2. The arbitrary-base centralizer quotient theorem supplies an actual
   `HomogeneousQuotient` for every centralizer representative, with smooth
   structure morphism and quasi-affine inverse image over every affine
   open of the base.
3. The unconditional diagonalizable normalizer quotient theorem over every
   commutative ring establishes `DiagonalizableNormalizerQuotientLocalModels`.
   Its proof uses a finite torsion subgroup with exactly the same full
   normalizer, the quasi-affine closed-embedding model, and its finite free
   character-automorphism quotient. The resulting actual orbit map has
   precisely the normalizer cosets as fibers on all scheme tests; the
   quasi-affine-target homogeneous orbit theorem gives the ring-local
   homogeneous quotient. The normalizer quotient descent theorem applies
   this input over finite affine refinements of the multiplicative-type
   splitting cover and glues over affine base opens. It gives the full
   normalizer-quotient clause, including smoothness and the exact relative
   quasi-affineness condition of the target.
4. For the Weyl quotient, the supplied normalizer is smooth and closed in
   the relatively affine ambient group, hence relatively affine. The
   original subgroup factors as a closed subgroup of the normalizer. The
   actual smooth closed centralizer model of that factorization represents
   the full preimage of the original ambient centralizer. The centralizer
   quotient theorem inside the normalizer supplies its homogeneous
   quotient. The Weyl quotient constructor equips it with a group
   structure and proves that its quotient map has this kernel and is the
   required fppf quotient, with etale, separated and quasi-compact
   structure morphism.

All subgroup functors, pullbacks, homogeneous quotients and fppf quotients
are the actual objects used by the imported target. Relative
quasi-affineness here means exactly that each affine base open has
quasi-affine inverse image, as the target defines. No finite-type or
Noetherian assumption on the base is imposed.

This is a derived assembly proof of the Library formulation of Conrad's
*Reductive group schemes* (2014), Theorem 2.3.1, first two sentences. Its
implemented proof route is the finite-character orbit construction and
fppf descent above. It preserves the target's full scheme-test meaning
and does not replace it with a statement about geometric points.
