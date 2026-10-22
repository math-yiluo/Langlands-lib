# Local supercuspidal finiteness statements

Worker 30 states finiteness of actual isomorphism classes of irreducible
admissible smooth complex representations of `GL_(n+1)(F)` satisfying
the actual Jacquet-vanishing supercuspidal condition. The field is a
Mathlib nonarchimedean local field with its specified compatible valuation
and topology. All positive ranks, including one, are covered.
The field and representation-carrier universes are independent.
There is no finite-dimensionality assumption on representation carriers.

`SupercuspidalCompactOpenFinitenessStatement` fixes a character of the
actual center and a compact open subgroup `K`. It asserts that the set of
supercuspidal isomorphism classes with that scalar center action and a
nonzero `K`-fixed vector is finite. The character need not be unitary.
The scalar-action condition is evaluated on actual representatives by the
proved class-invariant construction, so it cannot silently change with
a representative or an auxiliary presentation.

The original is I. N. Bernstein and A. V. Zelevinsky,
*Representations of the group GL(n,F), where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), Corollary 4.15,
printed page 41. It fixes a central character and a principal congruence
subgroup `N_i` and requires the corresponding invariant projection to be
nonzero. Section 3.1, page 28, states that these principal subgroups form
a compact-open identity-neighborhood basis. Any fixed compact open `K`
contains one of them. A nonzero `K`-fixed vector is then fixed by that
principal subgroup, and the set here is a subset of the finite set in
Corollary 4.15. This is the explicitly derived compact-open formulation,
not a quotation of a differently scoped theorem.

Sections 3.18--3.21 give the admissible cuspidal/quasi-cuspidal convention
and the relation to the subgroup vanishing conditions. Worker 23's
imported genuine class construction uses the actual Jacquet coinvariant
quotients for all proper block parabolics and their conjugates.
The source's intermediate word “finite” for certain representations is
not imposed as finite dimension of the whole representation carrier.
The original pages 28--43, including the complete proof in Section 4.16,
have been read.
Source ID `bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

`SupercuspidalBoundedLevelFinitenessStatement` fixes the same central
character and bounds the total first nonzero last-row-congruence level.
Infinity is excluded by a finite bound. The companion construction proves
that this bound is exactly nonzero invariants at level `b`.
The published `Conductor.levelOpenSubgroup` and its compactness theorem
supply the compact open subgroup required for the first assertion.
`SupercuspidalLevelFinitenessReductionStatement` separately records that
implication. No proof of any of these proposition definitions is supplied
in this statement contribution.

The last-row subgroups and level-zero convention are those of JPSS,
*Conducteur des representations du groupe lineaire* (1981),
Section 5.1, page 211. Source ID `jpss-1981-conductor`, SHA256
`986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
Pages 199--202 and 210--214 have been read. Calling this bound the
normalized epsilon-conductor bound requires separate supercuspidal
genericity and JPSS conductor identification with the additive character
of conductor zero. Those actual local-factor statements remain with
their existing owner. This module does not assume them or assert that
the first nonzero level is the general epsilon-factor conductor.

`SupercuspidalFinitenessStatement` is the conjunction of the three explicit
propositions. It assumes no local Langlands equivalence, relation descent,
numerical correspondence, finite-stratum count or local converse.
It is one component of Henniart's finite-witness argument, not the whole
argument or the final numerical surjectivity theorem.

The imported
`Langlands.Representation.Classification.SupercuspidalStrata`
constructs the actual supercuspidal strata and proves their intrinsic
quotient and finite-bound laws. Its independently published pair was
verified unchanged in Library commit
`ff093e1033dbbc93548c106d534ab35611d2c54e`: Lean SHA256
`fe7fddcd7c5c26e9aa39459062647525a05662f709939427ca8975b8480848a7`,
Markdown SHA256
`c87c5cceec8c90aa7384364805650918df3824cb9dacd3b0598d937d47b6e9f1`.
That construction assumes none of the present finiteness assertions.
Characters remain characters of the actual subgroup center; an application
starting with a character of field units must supply the scalar-center
identification explicitly.
