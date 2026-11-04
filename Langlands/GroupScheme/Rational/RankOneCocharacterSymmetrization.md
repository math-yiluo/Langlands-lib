# Integral cocharacter symmetrization in semisimple rank at most one

This internal bridge uses the actual quotient of rational normalizer points by
centralizer points. It applies over every field, in every characteristic, to a
connected reductive group with a split maximal torus whose actual roots are
pairwise integrally dependent.

For any normalizing rational point `n`, put `w = cocharacterAut (normalizingAut i n)`.
The definition `normalizerSymmetrizedCocharacter i n ν` is the integral
cocharacter `ν - w ν`. The actual relative Weyl quotient has order at most two,
by the published `Rational.RankOneWeylQuotient` results. Its published action on
the entire integral cocharacter lattice therefore gives `w² = 1`, including
the central directions. It follows that `w (ν - w ν) = -(ν - w ν)`.
No division by two or Lie algebra identification occurs.

A nonidentity class, if supplied, negates every actual root: the published
rank-one root-span action has a single global sign, and the published
reductive faithfulness excludes the identity sign. Injectivity of integral
characters into their rationalization turns this into the exact integral
root equality. Invariance of the lattice pairing then proves that every
root pairs with the symmetrized cocharacter as twice its pairing with `ν`.
The theorem does not assert that a nonidentity class exists.

Finally, `groupHom_cocharacterAut_comp` turns the exact cocharacter equality
into an equality after conjugation in the ambient group scheme.
`Dynamic.unipotent_eq_comap_of_iso` gives the resulting equality of dynamic
unipotent subgroup functors. This equality holds on all test schemes and
retains no premise identifying Lie algebras.

These are derived internal consequences of the published actual quotient
order bound, quotient actions, root-span sign theorem, reductive faithfulness,
and dynamic functoriality. They do not prove positive-root uniqueness,
existence of a nontrivial Weyl representative, or any Borel-normalizer
prerequisite. The dependency closure avoids `RegularCocharacterBorelStatement`,
`ParabolicDynamicStatement`, `RankOneSolvableObstructionStatement`, and
`RankOneBorelDynamicStatement`.
