# The modular character on actual norm-one adelic points

This internal adapter implements the closed normal subgroup step of
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §3.6,
Lemma 3.6.4, printed pp.89–90. It uses the Library's independently developed
closed-normal modular-character comparison. The October 2026 errata does
not correct §3.6.

The declarations are in `Langlands.Global.AdelicGroupPoints`, for arbitrary
`F : Type u` with its number-field structure and an affine, locally finite
type group scheme `G` over `F`. They retain the existing full adelic point
topology, Borel structures, actual algebraic characters and norm-one subgroup.
Smoothness and connectedness are not needed for this reduction.

`normOneAmbientModularCharacter F G` is the monoid homomorphism obtained by
restricting the full adelic group's modular character to the actual
`normOneSubgroup F G`.
`normOneAmbientModularCharacter_eq` identifies it with the subgroup's intrinsic
modular character. The proof applies `modularCharacter_normalSubgroup` to the
closed normal norm-one subgroup. Borel structures on the auxiliary left-coset
space and quotient group are chosen locally; the original group and subgroup
structures are retained.

Suppose an actual `F`-rational algebraic character `χ` satisfies

\[
\Delta_{G(\mathbb A_F)}(g)=|\chi(g)|_{\mathbb A_F}
\]

for every actual adelic point `g`, where the right side is the existing
`characterNorm F G χ g`, coerced from positive units to nonnegative reals.
`normOneAmbientModularCharacter_eq_one_of_characterNorm` proves that the
restricted character is trivial, by membership in the intersection of all
character-norm kernels.
`modularCharacter_normOneSubgroup_eq_one_of_characterNorm` transfers this
to the intrinsic subgroup character.
`normOneHaarRightInvariant_of_characterNorm` then proves right invariance of
the fixed `Measure.haar` on the actual subgroup: Haar uniqueness expresses its
right translate as the modular scalar times itself, and that scalar is one.

The comparison displayed above is an explicit premise. This adapter does
not prove that premise for the actual adelic group, and does not prove the
universal `AdelicHaarUnimodularityStatement`. The analytic comparison and
reductive determinant triviality remain separate obligations.
