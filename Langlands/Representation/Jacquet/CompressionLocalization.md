# The actual localization of compact compression and Jacquet fixed vectors

Worker 1755, with reuse guidance from Worker 1751. Derived constructions for
Renard 2026 VI.9.1, the two localization
lemmas on printed pp.196–197 / PDF pp.202–203, and their use in VI.9.2,
printed p.199 / PDF p.205. Source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This draft constructs the actual localization equivalence without a
finite-dimensionality, admissibility or finite-generation hypothesis.
It uses a compact open subgroup, the published abstract Iwahori contraction
conditions, a normalizing Levi subgroup, and an element central in that Levi.
More precisely, `N`, `M` and `Nbar` are actual subgroups of an arbitrary
topological group, `M ≤ normalizer N`, and
`IsIwahoriContraction K N M Nbar g` supplies the factorization, membership
`g ∈ M`, and the two contraction/exhaustion conditions. Centrality is the
explicit condition `∀ m ∈ M, m * g = g * m`.

The kernel of the actual fixed-vector Jacquet quotient is locally killed by
compression powers, by the published power-kernel equality. Every Jacquet
fixed vector has some positive-direction translate in the quotient image:
choose a representative, contract the opposite factor into its stabilizer,
use Levi fixedness of its quotient, and average over the compact subgroup.
The finite orbit mean preserves the constant quotient value.

A central group element acts invertibly on every subgroup fixed-vector
space. Its action is restricted using a genuine representation equivalence.
For the unnormalized Jacquet action this gives the target automorphism.
The fixed-vector quotient intertwines actual compact compression with that
automorphism.

The generic comparison uses the existing actual localized-module factor.
Local nilpotence of the kernel proves injectivity on fractions, and
power exhaustion proves surjectivity. These generic helpers and
`localizationEquivOfKernelExhaustion` are internal ordinary-unital-module
consequences over any commutative ring. The coefficient, source and target
universes are independent; the localization carrier has universe the maximum
of coefficient and source universes. The generic comparison assumes an
actual target automorphism, an intertwining map, local nilpotence of its
kernel, and forward-power exhaustion. It does not assume the map injective
or surjective.

`centralFixedVectorsEquiv` is also defined over any commutative ring and
has the explicit forward action and power application laws.
`fixedJacquetCentralEquiv` specializes it to the complex unnormalized
Jacquet action. The geometric lemmas
`fixedJacquetMap_kernel_locally_nilpotent`,
`fixedJacquetMap_power_exhaustion`,
`fixedJacquetMap_intertwines_centralEquiv`, and
`fixedJacquetCentralEquiv_power_exhaustion` verify all the inputs of the
generic comparison using the published concrete maps.

The resulting `Jacquet.compressionJacquetLocalizationEquiv`
is complex-linear between
`Renard.EndomorphismLocalization.Localized (compressedAction ρ hρ K hK g)`
and `fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)`.
The group and representation-carrier universes are independent.
Its `_iota` and `_intertwines` laws prove that this equivalence
takes the canonical localization map to the actual fixed-vector quotient
and intertwines the actual localized endomorphism with the restricted
Levi action.

This module asserts no eventual stability or uniform exponent. In VI.9.2
finite generation over the coefficient ring must still be supplied for
both the compact fixed vectors and the Jacquet fixed vectors, with their
compatible coefficient actions. These are constructions and elementary laws
of the actual localization comparison, rather than a proof of the host task's
uniform stabilization proposition. The broader topological-group and
commutative-ring settings of the internal helpers are derived scope; no new
generality is attributed verbatim to Renard.
