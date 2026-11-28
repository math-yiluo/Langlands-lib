# Proper parabolic induction has no irreducible supercuspidal subquotient

`leviInductionNoSupercuspidalSubquotient` proves
`LeviInductionNoSupercuspidalSubquotientStatement` in
`Langlands.Aubert.General.RepresentedParabolic`. The source is the Lemma of
David Renard, *Représentations des groupes réductifs p-adiques*, VI.5.2,
printed p. 173, PDF p. 179 of the French edition dated 9 July 2026. The
registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Suppose an irreducible supercuspidal representation `σ` of `G(F)` is the
quotient of an invariant subspace of the normalized induction. The special
compact basis theorem gives compact smooth-dual coefficients for the
restriction of `σ` to the common norm kernel via
`compactRestriction_of_isSupercuspidal`. Compact induction of this whole
restriction is projective by `rationalNormKernelSummandInduction_projective`
and supercuspidal by `isSupercuspidal_rationalNormKernelSummandInduction`.
Both results apply to the identity embedding of the restriction.

Compact-induction reciprocity sends the identity of the restriction to a
map from the projective object to `σ`. The identity is nonzero because
`σ` is irreducible, so the corresponding map is nonzero. Projectivity lifts
it through the given quotient of the invariant subspace. The lift followed
by the inclusion gives the nonzero map into the normalized induction that
Renard obtains from the supercuspidal summand. Since the parabolic is
proper, `hom_induction_eq_zero_of_supercuspidal` forces this composite to
vanish by normalized Frobenius reciprocity.
