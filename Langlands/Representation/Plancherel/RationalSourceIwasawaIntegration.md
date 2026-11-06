# Actual Iwasawa integration at the common compact normalization

Lean module: `Langlands.Representation.Plancherel.RationalSourceIwasawaIntegration`,
namespace `Langlands.Plancherel.RationalDynamicSource`.

The setting is the canonical rational-point group of an affine, locally
finite type group scheme over any nonarchimedean local field. The field
universe is arbitrary. A field-defined cocharacter supplies the actual dynamic
parabolic `P`, Levi `M`, and radical `U`. The topology is
`rationalPointTopology`, and measures use its Borel sigma algebra. No
characteristic, splitness, or quasisplitness restriction is imposed.

For a supplied compact open `K`, `compactHaar` is the existing
`subgroupCompactOpenHaar` on `K` itself. It has total mass one, as proved by
`compactHaar_univ` and recorded in its probability-measure instance. This uses
the same compact-intersection normalization as the existing `ambientHaar`,
`parabolicHaar`, `leviHaar`, and `radicalHaar`.

`iwasawaMap` is literal multiplication `(p,k) ↦ p*k`, and `iwasawaMeasure`
is its pushforward of `parabolicHaar × compactHaar`. The measure is defined
without a coefficient or an assumed integration identity.
`iwasawaMeasure_self` proves that it gives `K` mass one: because `k ∈ K`,
`p*k ∈ K` is equivalent to `p ∈ K`, so the inverse image of `K` is the
parabolic trace of `K` times all of `K`.

`ambientHaar_eq_iwasawaMeasure` assumes precisely the displayed actual
factorization

`∀ g, ∃ p : P, ∃ k : K, g = p*k`.

The published theorem
`CompactFactorization.exists_pos_eq_smul_map_mul_prod` gives proportionality
to the original ambient Haar. Evaluation on `K`, of mass one for both
measures, forces the scalar to one. The proof requires no reductivity,
smoothness, compact-limit stability, or ambient or Levi right invariance.
`lintegral_eq_parabolic_compact` then proves the `P,K` iterated lower
integral formula for every measurable nonnegative extended-real function
using measurable change of variables and Tonelli.

For the three-factor formulas there is an additional explicit premise:
the actual `Dynamic.limitHom` takes `P ∩ K` into `K`.
`lintegral_eq_levi_radical_compact_of_limit_stable` applies the existing
normalized parabolic product comparison to a measurable partial integral.
It gives the `M,U,K` order. Finally,
`lintegral_eq_iwasawa_source_order_of_limit_stable` proves

`∫⁻ g, f(g) dg = ∫⁻ u, ∫⁻ m, inverseLeviModulus(m) * ∫⁻ k, f(u*m*k) dk dm du`.

The density is the inverse of the existing actual radical conjugation
character, defined independently of `K`. The proof uses the published
`IsConjModulus` law to change `m*u` to `u*m`, proves measurability of the
weighted pair, and uses Tonelli to obtain the source order. There is no
gamma factor in this first integration formula.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), I.1, first formula (2) and the
common-compact normalization paragraph, printed p.240 / PDF p.6,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`. The source treats complex locally constant
compactly supported functions and its chosen special maximal compact.
The measurable nonnegative formula and the literal pushforward comparison
here are derived internal extensions. The generic published
`HarishChandraSchwartz.IwasawaIntegration` proves a related abstract formula
with `dk` presented as restricted ambient Haar; this module supplies actual
dynamic subgroups and independently normalized subgroup Haar, with the
source's integration order.

This contribution retains Iwasawa factorization and, for the three-factor
formulas, compact-limit stability as visible hypotheses. It does not construct
the source special compact or prove these structural hypotheses for every
reductive group. The Bochner extension, source gamma independence, spectral
normalizations, and Plancherel conclusions remain separate obligations.
