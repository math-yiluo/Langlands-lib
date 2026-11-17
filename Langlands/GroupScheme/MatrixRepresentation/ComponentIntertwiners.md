# Intertwiners from the identity component and rational points

Over an algebraically closed field, rational translates of an actual open
identity-component subgroup form an open cover of any group scheme locally of
finite type. `IdentityComponent.componentTranslate` is the actual map from the
subgroup obtained by composing its inclusion with left translation by a rational
section. `componentTranslateCover` constructs the actual scheme open cover.
For a point of the group, choose a rational section in the same component.
Translating the point by the inverse section places it in the identity component,
where the inclusion supplies a lift. Translation back recovers the original
point. No reducedness or smoothness assumption is used.

For an affine group, `intertwines_iff_universal_pointMatrix` characterizes actual
all-affine-test equivariance by the single matrix identity in global sections at
the universal scheme point. Natural pullback of matrix entries and the affine
sections/algebra comparison give the converse.

`intertwines_of_identityComponent_and_rationalMatrix` assumes affine source and
subgroup, an open subgroup inclusion whose range is the actual identity set,
and local finite type of the source. A ground-field matrix that intertwines the
restrictions to this subgroup and intertwines every rational-point matrix then
intertwines the actual group-scheme representations on every affine test. On
each translated subgroup, the matrix of the translation factors as the constant
rational matrix times the subgroup matrix. The two assumed intertwining
identities therefore prove the desired identity there. The scheme open cover
separates global sections, which proves the universal identity and hence actual
equivariance. This retains the nilpotent structure in every component.

## Provenance

This internal derived gluing argument supplies the all-test bridge needed when
applying finite-quotient averaging to group-scheme representations. The identity
component and geometric component interpretation follow Milne, *Algebraic Groups*
(2022 corrected reprint), Proposition 1.34, printed p.17, and Proposition 2.37,
printed p.51. The source is registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
Both passages were read in the retained original. The full official errata
snapshot `milne-2022-algebraic-groups-errata-2026-11-04` corrects rational-point
surjectivity over the separable closure in the construction preceding 2.37;
this module instead assumes an algebraically closed field and uses the
published rational-representative theorem only in that scope.

The proof uses the existing scheme translation, point-matrix, open-cover and
all-test-intertwiner APIs; it makes no rational-point density inference for a
nonreduced scheme. It does not construct an averaged projection or prove the
multiplicative-type classification in Nagata's theorem.
