# Non-supercuspidal subquotients for nonconjugate Levis

`leviJacquetInductionNoSupercuspidal` proves
`LeviJacquetInductionNoSupercuspidalStatement` for arbitrary represented
parabolics `P = MN` and `Q = LU`. If `M` and `L` are nonconjugate and `ρ` is
supercuspidal, every irreducible subquotient of `r_Q^G i_P^G ρ` fails the
supercuspidality test on `L`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.5.3(ii), printed p.173 / PDF p.179.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof applies `leviJacquetInductionNoSupercuspidal_of_geometricLemma` to
`representedGeometricLemma` and `leviInductionNoSupercuspidalSubquotient`.
The deduction locates the given irreducible subquotient in a geometric-lemma
grade. When the target intersection parabolic in `L` is proper, VI.5.2
excludes supercuspidality because the grade is a normalized induction from
that parabolic. When the target intersection parabolic is full, the source
intersection parabolic in `M` is proper since two full intersections would
provide the excluded conjugacy. Supercuspidality of `ρ` then makes its
intersection Jacquet module zero, so the grade has no irreducible
subquotient.
