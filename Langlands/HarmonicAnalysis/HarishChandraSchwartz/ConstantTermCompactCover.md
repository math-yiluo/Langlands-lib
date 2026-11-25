# Compact double-coset reduction for the constant-term estimate

This is a derived implementation of the compact
double-coset reduction in the proof of Waldspurger's Proposition II.4.5,
printed p.262. The structural compact subgroup may differ from the subgroup
defining the spherical function and from the subgroup preserving the height.
The module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermCompactCover`
defines `ConstantTermCompactCoverStatement.{u}` and proves it by
`constantTermCompactCover`, at arbitrary carrier universe `u`.

The main theorem `constantTermEstimate_of_doubleCosetCover` assumes that a
subgroup `K_M` and a set `S` cover `M` as `K_M S K_M`, the conjugation modulus
relation on the integrated subgroup `U`, triviality of that modulus on `K_M`,
and a constant-term estimate on `S` for each real decay exponent. It extends
the estimate to all of `M` when translations by `K_M` uniformly dominate each
weighted kernel `Ξ(g)(1 + σ(g))^(-r)` and each Levi kernel
`Ξ^M(m)(1 + σ^M(m))^(-r)`. These domination constants are finite nonnegative
real numbers and may depend on `r`.

For `m = k₁ s k₂`, conjugating the integration variable by `k₂` preserves the
measure because its modulus is one. The ambient kernel is bounded by `A`
times the kernel at `s u`. Apply the estimate at `s`, then bound its Levi
kernel by `B` times the kernel at `m`, using the Levi translation bound at
`k₁⁻¹, k₂⁻¹`. The resulting constant is `A c B`. The main theorem does not
assume that either kernel is invariant under the covering subgroup.

Two helpers explain how these kernel hypotheses arise.
`UniformTranslationBound.mul_one_add_rpow` proves that multiplying a
nonnegative function satisfying `UniformTranslationBound` by any real power
of `1 + σ` preserves that property when `σ` is nonnegative, symmetric under
inversion and subadditive. The height at `a g b` and at `g` is comparable
with factor `1 + σ(a) + σ(b)`; real powers give the absolute value of the
exponent in the comparison factor. `rpow_le_mul_rpow_of_comparison` proves
the scalar real-power step for positive bases.

`UniformTranslationBound.exists_uniform_mul` proves uniformity of
translations on a compact subgroup when the nonnegative function is left
and right invariant under some open subgroup. It applies the published
compact left-translation result both to the function and to its inverse
pullback `g ↦ Ξ(g⁻¹)`, and combines the two constants. Thus a compact
covering subgroup need not be the subgroup of local invariance.

These are abstract deductions. They do not establish a rational-group
unipotent estimate, a Levi lower bound or weighted integrability, and they
do not prove `RationalConstantTermEstimateStatement`. Their source motivation
is the first reduction in Waldspurger II.4.5; the extension to bounded
translations is derived here from that change-of-variables argument.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), literature ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
Proposition II.4.5 and its proof, printed pp.262–263.
