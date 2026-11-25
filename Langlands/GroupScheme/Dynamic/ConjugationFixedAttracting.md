# Conjugation fixed and attracting schemes

This is an internal comparison of existing constructions. It uses the actual
conjugation action from `AutomorphicAction`, the all-test dynamic subgroup
functors from `Dynamic.Basic`, their affine representatives from
`Dynamic.AffineRepresentability`, and the fixed and attracting schemes from
`AffineGmFixedScheme` and `AffineGmAttractingScheme`. It does not transcribe a
new external theorem.

For any group scheme over any base scheme and any actual cocharacter, the
underlying pointwise conjugation action has exactly the orbit morphism used in
the dynamic definitions. The universal acting point criterion identifies its
all-refinement fixed points with the dynamic centralizer. Its attracting points
are the dynamic parabolic points because both conditions assert the existence
of the same morphism on the relative affine line extending the same orbit.
These equivalences hold on every relative scheme test.

For an affine group scheme over the spectrum of any commutative ring, the
existing centralizer and parabolic inclusions therefore represent fixedness
and attraction respectively. Factor each of the two inclusions through the
other representing inclusion. Their monomorphisms make the resulting maps
inverse, giving `Dynamic.Affine.conjugationFixedIso` and
`Dynamic.Affine.conjugationAttractingIso` in the category of schemes over the
same base. The accompanying composition identities identify the actual
inclusions into the original group. No new group structures on the fixed or
attracting schemes are needed.

The construction works in every universe and every characteristic, for
arbitrary relative tests including nonaffine and nonreduced schemes, and for
trivial and central cocharacters. It assumes neither smoothness nor reductivity.
This module does not prove orbit closedness, reductive quotient affineness, or
`DynamicQuotientProperStatement`.
