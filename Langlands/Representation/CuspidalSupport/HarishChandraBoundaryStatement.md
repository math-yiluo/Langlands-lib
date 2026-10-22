# Smooth dual restriction and rank zero for Harish-Chandra's criterion

Author: Worker 200.

This statement pair isolates two elementary obligations of the full published
`Langlands.CuspidalSupport.LeviHarishChandraTheorem` without changing that
proposition or its imports. The conjunction
`HarishChandraBoundaryStatement.{uF,uV}` has two independent universes: one for
the actual p-adic field carrier, and one for representation carriers.

`DeterminantUnitSmoothDualStatement` quantifies every prime `p`, actual
`PadicField F`, compatible `T : F.TopologicalData`, rank `n`, block shape `B`,
complex module `V`, representation `ρ` of the product Levi, and algebraic linear
functional `ℓ`. Under the topology supplied by `T`, it asserts that `ℓ` is a
smooth vector for the dual of `determinantUnitRestriction T B ρ` if and only if
it is smooth for `ρ.dual`. The original representation need not be smooth.
This is a comparison of the actual dual actions and existing `IsSmoothVector`
predicate, not a replacement for the restricted-dual condition in the full
target.

`LeviHarishChandraRankZeroStatement` is exactly the rank-zero specialization
of the existing full target, with every smooth complex representation of every
`B : BlockShape 0`. It asserts the equivalence of actual quasicuspidality and
compact smooth-dual coefficients on the determinant-unit subgroup. No
irreducibility, admissibility, dimension or central-character hypothesis is
added. Both propositions are definitions returning `Prop`; this pair contains
no proof of either proposition.

## Provenance and mathematical justification

The original source is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local field*,
Russian Mathematical Surveys 31:3 (1976), 1–68 (BZ76), registered as
`bernstein-zelevinsky-1976-representations-gln`. Its retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Worker 200 read printed/PDF p.26, pp.28–31 and pp.34–35 directly. No source
errata note was found in the current Library.

In the proof of Theorem 3.21, (3) implies (4), on p.35, BZ76 observes that
restriction to the open subgroup `G°` leaves the smooth contragredient space
unchanged. The first proposition is the concrete product-Levi version of this
observation. Its elementary justification is that an open subgroup of an open
subgroup is open in the ambient group, and intersection restricts an ambient
open subgroup. Dual pullback agrees with pullback of the dual because the
subgroup inclusion preserves inverses. None of this uses smoothness of `ρ`.
The openness of the actual determinant-unit subgroup is already proved in
`Langlands.Representation.CuspidalSupport.DeterminantUnit`.

The second proposition is an internal rank-zero extension, not a separate
claim made in BZ76. Positivity of block sizes forces `B` to have no blocks.
Its Levi and determinant-unit subgroup are therefore singleton groups. Every
refined parabolic is the whole group, so quasicuspidality is vacuous. Every
coefficient has compact support because its domain is a compact singleton.
This argument works for an arbitrary carrier dimension.

The coefficient convention is exactly the Library's
`matrixCoefficient ρ ℓ v g = ℓ (ρ g v)`. The source's inverse-element
convention does not enter either proposition. These statements isolate
boundary obligations only; the positive-rank Harish-Chandra equivalence and
its averaging and Cartan argument remain separate proof obligations.
