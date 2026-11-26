# Permuting the inducing blocks in real ordinary normalized generation

`realOrdinaryOrderedGenerationReduction` proves
`RealOrdinaryOrderedGenerationReductionStatement`. Ordinary normalized
generation on Langlands-ordered lists implies
`RealOrdinaryNormalizedGenerationStatement` for the supplied lists.
Langlands order here means non-increasing real parts of block exponents,
the convention of the Library's upper triangular induction.

For an irreducible real standard module of a list `ds`, the proved
constituent-permutation theorem makes this module a quotient of a
compact and Lie stable subspace of the standard module of any
permutation `es`. The compact action on the latter module is
semisimple, by compact finiteness and continuity of its coefficients.
Over the compact group algebra the quotient therefore splits. The
resulting compact-equivariant injection of the module of `ds` into
that of `es` is surjective by admissibility and the reverse compact
injection from block permutation. Its image lies in the given stable
subspace, so that subspace is the whole module. The original quotient
map is then bijective and intertwines both actions.

Pulling back a coefficient map through a surjective intertwiner
preserves the coefficient hypotheses and its range. Applying this
in both directions gives equality of the two ordinary Whittaker
submodules at every additive scale, along with irreducibility of the
reordered module. Sort each parameter list and apply these equalities
and `realPairLFactor_perm`. The integrals are functions of the
coefficients, the quotient measure and, in equal rank, the Schwartz
test. With the two submodule equalities and equality of the pair
factor, both normalized generation conclusions transport to the
supplied lists.

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), uses
permutation of inducing characters and the resulting constituent
comparison in §15, pp. 108–109. The proof here is an internal
argument for arbitrary real blocks using the Library's
`realStandardConstituent_perm` and compact injectivity and
admissibility results. Source `jacquet-2009-archimedean-rankin-selberg`,
SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
