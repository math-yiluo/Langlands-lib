# Principal congruence and newvector levels

Worker 43 authored this derived construction. It uses the actual matrix
general linear group and the previously constructed last-row congruence
subgroups. It introduces no new conductor convention.

For a commutative ring `R`, ideal `I`, and positive rank `n + 1`,
`integralPrincipalCongruence n I` is the kernel of the homomorphism
`GL_(n+1)(R) → GL_(n+1)(R/I)` induced by the quotient ring map.
Its proved membership criterion requires every matrix entry minus the
corresponding identity entry to lie in `I`. Restricting this condition to
the last row proves
`integralPrincipalCongruence_le_integralCongruence`.
Both subgroups agree at rank one. Reduction modulo the unit ideal gives
the full integral group, including when the quotient ring is the zero ring.

For a subring `O` of a field `F`, `principalCongruenceSubgroup O n I` is
the image of this kernel under the actual inclusion of invertible
integral matrices into `GL_(n+1)(F)`. Injectivity of that inclusion gives
`map_mem_principalCongruenceSubgroup`. Taking images preserves the
containment in the last-row subgroup. Thus integrality means membership
in `GL(O)`, with both the matrix and its inverse integral.

`principalLevelSubgroup F n a` specializes the ideal to the `a`th power
of the maximal ideal of the supplied valuation's integer ring. Level
zero is the full integral group, and the levels are antitone. For
`a ≤ b`, `principalLevelSubgroup_le_levelSubgroup_of_le` proves
`P(b) ≤ K_1(a)`. The specialization to `b = max 1 a` supplies a positive
principal level even when `a = 0`.

The topology section proves that these are open subgroups when the
integer subring and ideal are open: the kernel is a finite intersection
of open entrywise congruence conditions, and the integral inclusion is
the previously proved open embedding. Over a compact Hausdorff integer
ring, that open subgroup is closed in the compact integral general
linear group, hence its image is compact. In the supplied
nonarchimedean local-field topology, `principalLevelOpenSubgroup`
packages openness and `isCompact_principalLevelOpenSubgroup` proves
compactness for every level. This uses the same integer ring, maximal
ideal, and existing matrix-group topology as the last-row construction.

For a representation over any commutative coefficient ring,
`principalLevelFixedVectors` is its actual invariant submodule for
`P(a)`. The subgroup containment gives an inclusion of `K_1(a)`-fixed
vectors into `P(b)`-fixed vectors whenever `a ≤ b`, preserving
nonvanishing. In particular,
`principalLevelFixedVectors_ne_bot_of_conductor_le` proves that a
representation with an explicitly supplied finite newvector level and
conductor bounded by `b` has nonzero `P(max 1 b)`-invariants. The
existence of a finite newvector level remains an explicit prerequisite.
No generic newvector theorem, dimension theorem, epsilon-factor identity,
or finiteness theorem for representations is assumed or proved here.

## Sources and provenance

The last-row subgroup and its level-zero convention come from
H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Conducteur des representations du groupe lineaire*,
Math. Ann. 256 (1981), 199–214, Section 5.1, page 211
(registered source `jpss-1981-conductor`, SHA256
`986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`).
The exact translation and positive-level block conditions are documented
in `Congruence.md`. Section 5.4, page 214, explains why finite
last-row fixed level must not be imposed on arbitrary nongeneric
representations.

The full reduction kernel and all containment and fixed-space arguments
in this module are elementary derived constructions. Their proofs use
Mathlib's `GeneralLinearGroup.map`, group-homomorphism kernels, ideal
quotients, subgroup images, and the already proved last-row membership
criterion. No external bounded-level finiteness result is invoked.
Independent uses of such a theorem must supply its own hypotheses and
proof.

The field and coefficient universes are independent, and representation
spaces have their own universe. The construction is algebraic and
requires no topology on the coefficient ring or representation space.
Only the compact-open certificates require a topology on the field,
with precisely the compatibility hypotheses shown in Lean.
It imports `Langlands.Representation.Conductor.Definitions`, which
in turn imports the congruence construction and the shared fixed-vector
interface.

The imported conductor pairs are published in Library commit
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`, and their published bytes
were verified against the inputs used here. This pair still requires
its own independent review and publication. Native compilation alone
does not establish either.
