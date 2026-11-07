# Negative scalar-rho eigen-rows from supplied highest-weight modules

This is a derived adapter on the original matrix representations. Fix a field
`k : Type u`, an affine group scheme `G` over `Spec k`, a supplied split pinning
`p` with finite root index, and the equality of the integral coroot span with
the whole cocharacter lattice. Write `rho` for its integral Weyl vector and
`nu` for the polarization of `rho`. No existence assertion for these inputs
is made here.

`exists_highestWeight_dual_extremalRepresentation` starts with any supplied
highest-weight matrix representation `rhoRep` of highest weight `lam`. It
constructs a matrix representation `sigma` with the same finite coordinate
index, integer exponents and an index `a`, and proves four properties:

- The actual cocharacter `groupHom nu` followed by the original torus inclusion
  and `sigma` is the diagonal cocharacter with those exponents.
- The exponent at `a` is strictly smaller than every other exponent.
- On every relative test scheme, the torus matrix entry `(a,a)` evaluates the
  character of weight `-lam`.
- The rational-point representation of `sigma` is irreducible if and only if
  that of `rhoRep` is irreducible.

The proof generalizes the construction in `HighestWeightExtremal` from integral
rho to the arbitrary supplied highest weight. Its existing character-basis
lemma gives a unique highest coordinate and strict maximality against polarized
rho. Conjugation by the basis coordinate point makes the original torus action
diagonal on every relative test scheme. The actual dual negates the characters
and exponents, making that coordinate the unique minimum. The existing
cocharacter comparison proves the diagonal identity. The equivalences from
`RationalDualConjugateIrreducibility` prove the last property over the same field;
it is not deduced by silently replacing actual irreducibility by rational
irreducibility.

`exists_scalarRho_eigenrow` specializes to highest weight `m • rho` for any
natural `m`. Its inputs include both the highest-weight predicate and rational
irreducibility of the supplied representation. It produces an irreducible
rational representation `sigma` on the same coordinate index and a nonzero
row `Pi.single a 1`. On every relative scheme `V`, at every point `h` of the
canonical represented polarized-rho parabolic, the row multiplied by the
original point matrix equals its scalar multiple by the value at `h` of the
`m`-th power of the canonical negative-rho coordinate.

For this specialization, the original maximal torus represents the dynamic
centralizer by `CanonicalRhoDynamics`. The parabolic is the existing closed
affine dynamic representative. The unique minimum gives its actual rational
character and row identity by `DynamicExtremalLines`. Restriction of that
character to the torus is identified using its diagonal entry and the weight
`-(m • rho)`. Injectivity of restriction from the closed parabolic, proved by
`Dynamic.ParabolicCharacters`, identifies it with `m` times the extended
negative-rho character. `HomogeneousCharacterProducts.characterCoordinate_nsmul`
then identifies its coordinate with the literal power used in the conclusion.
The standard row is nonzero by evaluation at `a`; scalar extension of the row
is exactly `scalarMap_single_one`.

`ScalarRhoEigenrowData p hspan n m` packages the resulting representation on
the original index `n`, its distinguished index, rational irreducibility,
nonvanishing standard row and the full relative-test eigen-row identity.
`scalarRhoEigenrowData` selects this package from the supplied highest-weight
representation and its rational irreducibility proof, using the preceding
existence theorem and classical choice. It introduces no extra mathematical
premise or change of dimension.

All point-matrix and row identities quantify over arbitrary relative test
schemes, including nonaffine and nonreduced ones. Algebraic closedness is not
an assumption of this adapter. It does not supply the pinning, full coroot
span or highest-weight representation, prove dimension bounds or coefficient
exhaustion, or prove `SteinbergBigCellStatement`. The general construction and
its specialization are internal consequences of the named Library interfaces;
no external literature assertion is used as an additional premise.
