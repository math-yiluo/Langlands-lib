# Rational invertibility of actual geometric polarizations

`Langlands.AbelianScheme.Rosati.rationalInverse` proves exactly the existing
`Langlands.AbelianScheme.Rosati.RationalInverseStatement`, with its single
universe parameter unchanged. For an actual abelian scheme over an
algebraically closed characteristic-zero field, every actual geometric
polarization becomes an isomorphism in the existing rational Hom category.
The tensor, Picard and constructed-dual prerequisites remain exactly those
in the imported statement. No inverse, kernel annihilator, dimension,
trace or positivity premise is added.

The source correspondence is J. S. Milne, *Abelian Varieties*, January 2,
2022 author revision, section 17, printed/PDF page 35, opening paragraph:
a polarization is an isogeny and has an inverse in rational Hom. The
registered source is `milne-abelian-varieties-1986-author-2022`, SHA-256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The original page and complete registered errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25` were read. All listed
corrections are incorporated in this revision.

The implemented proof composes existing published geometric and categorical
results. The first component of the actual `IsPolarization` predicate says
that the polarization is finite, flat and surjective. Its scheme-theoretic
kernel is finite over the field because its structure map is the base
change of that finite morphism along the target unit section, using
`GroupScheme.kernel_isPullback_scheme`.

The kernel is commutative as a subgroup of the source abelian scheme.
`GroupScheme.exists_pow_eq_one_of_isFinite`, imported from
`CentralIsogeny.KernelTorsion`, therefore gives a positive natural number
that kills its points on every test scheme. This theorem assumes only
finiteness and commutativity of this group scheme; no central-isogeny
hypothesis is used. Applying it to the identity point of the kernel itself
and the published multiplication formula shows that multiplication by
the same nonzero integer is the zero group-scheme homomorphism.

Finally, `AbelianScheme.isogenyInverseStatement_of_commGroupScheme` applies
the published `CommGroupScheme.isogenyInverse` to the actual bundled
abelian schemes and the polarization. That inverse theorem descends
multiplication along the finite flat surjection and divides the resulting
homomorphism by the nonzero integer in the rational tensor Hom group.
Thus its conclusion is exactly the required
`IsIso ((rationalization _).map lam)`. The kernel annihilator is derived
inside the proof. This argument needs no additional use of algebraic
closedness or characteristic zero, but the exported theorem retains the
exact existing statement and its full universe scope.
