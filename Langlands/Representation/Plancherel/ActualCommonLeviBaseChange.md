# Actual original common-Levi integrals under translated base change

This internal adapter establishes an elementary original-integral square
needed for the representative and orbit-base comparisons of Waldspurger
(2003), V.3 formula (1), printed p.295 / PDF p.61, registered as
`waldspurger-2003-plancherel`. It specializes the published original
standard-integral base-change theorem to the actual dynamic common-Levi
families. It defines no replacement integral or continuation family.

Work over an arbitrary nonarchimedean local field, with an affine locally
finite type group scheme and cocharacters `χ, ψ, ψ'` whose indicated
centralizer subgroup functors are equal. The literal base Levi is
`levi χ`. All rational-character norms and point topologies are the actual
ones. The two smooth inducing objects have independent carrier universes.
Neither irreducibility nor admissibility nor connected reductivity is
needed for this elementary square; squared-modulus compatibility is
supplied explicitly where it is required to define the actual standard
operators. The source compact open `K` and its compactness proof are the
existing inputs defining the original quotient-integration measure.

Given a full unramified parameter `τ` and an inducing equivalence
`a : A_τ ≃ B`, `inducingEquiv χ τ z a` constructs the equivalence
`A_(τ*z) ≃ B_z` from the published `transportedBaseTwistEquiv` in the
actual character chart `parameterHomeomorph χ`. It uses the actual smooth
twists and their open-kernel proofs. Its vector map is the given inducing
map `a`; no coefficient-space equivalence is chosen.

`fullDomain_iff` proves that `τ*z` is in the actual full original domain
for `A` precisely when `z` is in the actual full original domain for `B`.
This is the complete scalar-integral and original-carrier representability
domain, not a restricted denominator locus. The proof specializes
`standardIntertwiningFullDomainRegion_translation_iff` to the actual
common decomposition, radical, parameter homeomorphism, full norm family
and `pairQuotientMeasure K hK ψ ψ'`. The same measure is retained on both
sides. No openness or nonemptiness is inferred for either full domain.

`originalSquare` proves that the actual original standard integral
`pairFamily` commutes with `inducedMap` for `inducingEquiv`, on every source
vector at the corresponding parameters. Membership of `z` in the domain
for `B` is the sole displayed convergence premise; the theorem obtains
membership of `τ*z` for `A` from `fullDomain_iff`. Its proof specializes
`standardInductionIntertwinerFamily_natural` with the actual source
radical Haar measure, intersection Haar measure, compatible quotient
measure and squared-modulus proof. Thus its square is a theorem about the
actual standard integrals, not an assumed square for freely chosen
operator families.

The original same-parameter representative square and its full-domain
transport already exist as `DynamicCommonLeviCompact.pairFamily_natural`
and `pairFullDomainRegion_equiv`. Together with this translated square,
these provide the original hypotheses used by the published
`continuedInductionIntertwiner_natural` and
`continuedInductionIntertwiner_baseChange` machinery. In applications one
still displays the independent continuation data and a common nonempty
open starting region with the appropriate translated inclusions; those
propagation theorems then compare independent denominators on the common
regular locus. This module makes no continuation-existence or nonempty-open
claim and proves no all-unitary extension theorem. It changes no compact
probability normalization, source formal degree or quotient measure.
