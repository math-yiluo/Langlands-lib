# Bilinear bounds from unique functional factors

This internal adapter combines the published functional-length argument with
the bilinear bound along actual finite filtrations. The two representation
carriers have independent universes. The two character-functional predicates
may use different subgroups and characters of the same group.

`gradedExceptionSet` takes the finite union of supplied exceptional sets over
all pairs of graded positions. Its membership lemma identifies membership
with membership in at least one pair's set. Consequently, being outside the
union implies being outside every pair's set. Repeated factors retain their
positions; no quotient by isomorphism classes is taken.

`length_le_one_of_unique_functional_factors` assumes that exactly one position
in each filtration has a nonzero character functional. It also assumes that a
graded bilinear space can have nonzero length only if both factors have their
respective functionals, and that a pair with both functionals has bilinear
length at most one. Uniqueness of the positions forces every other pair's
length to vanish. The actual single-pair filtration bound then gives total
bilinear length at most one.

`exists_exception_length_le_one_of_unique_functional_factors` assumes the two
pairwise implications hold outside a finite set for each pair, for an arbitrary
parameter type, spectrum map, and family of covariance functions. It chooses
all those sets and takes their finite union. This produces one exceptional
set before quantifying over the parameter, hence also before any bilinear
forms are chosen. The previous theorem applies pointwise outside the union.

`exists_exception_length_le_one_of_functional_equiv` derives the two unique
positions from `FunctionalLength.existsUnique_hasFunctional_factor`: the
representations are smooth, each relevant subgroup is a limit of compact
subgroups in the Library's compact-containment sense, character values are
locally constant, and each total functional space is linearly equivalent to
the complex numbers. It then applies the finite-exception theorem. The
published `InvariantBilinear.exists_smul_eq_of_length_le_one` converts the
conclusion into proportionality to any nonzero covariant bilinear form.

The provenance is internal finite-set and module-length reasoning. In
particular, the pairwise rigidity and length bounds are explicit hypotheses.
This module supplies neither filtrations nor those representation-theoretic
inputs, and does not prove the JPSS trilinear uniqueness statement.
