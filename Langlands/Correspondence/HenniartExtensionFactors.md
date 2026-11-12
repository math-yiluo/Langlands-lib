# Pair factors and the extended stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionFactors`,
namespace `Langlands.Henniart.Extension`.

Henniart (2000), §4.3 (4.2 c), "découle aussi de 3.8"), extended by unramified
twists as in Henniart (1993), §4.4:
`ε(π × π_ρ |·|^u, s, ψ) = ε(π × π_ρ, s + u, ψ) = ε(σ ⊗ ρ, s + u, ψ) = ε(σ ⊗ ρ |·|^u, s, ψ)`.

## Unramified exponents

`exists_unramifiedExponent`: for `z ∈ ℂ^×` there is `u ∈ ℂ` with `q^(-u) = z` and
`fieldUnramified K z = |·|^u` pointwise, where `q` is the residue cardinality
and `|·|` the published normalized absolute value. Take
`u = -log z / log q`. Then `q^(-u) = exp(log z) = z`. Since
`|x| = q^(-ord x)` (published `normalizedAbs_of_ne_zero`),
`|x|^u = exp(ord(x) log z) = z ^ ord(x)` (`Complex.exp_int_mul`).

`comp_C_mul_X_comp`: `(P(a X))(b X) = P(a b X)`.

## The GL side

`isSupercuspidalPairLPolynomial_unramifiedTwist`: twisting the two members of a
supercuspidal pair by `fieldUnramified z ∘ det` and `fieldUnramified z' ∘ det`
turns a JPSS L-polynomial `P` into `P(z z' X)`. Apply the published
`RankinSelberg.unramifiedTwistLFactor` twice to representatives, with the
exponents of the previous lemma. The self-dual measure is packaged as a
`LocalFactor.PadicAbelian.SelfDualHaar`.

`isSupercuspidalPairEpsilonFactor_unramifiedTwist`: the same twists turn an
epsilon certificate `(c, m)` into `(c (z z') ^ m, m)`, given
`RankinSelberg.UnramifiedTwistEpsilonStatement` (applied twice). The coefficient
`c q^(-mu) q^(-mu')` equals `c (z z') ^ m` by `Complex.cpow_mul_int`.

## Generators

`LocalWeil.isArithmeticPairEpsilonFactor_of_generator` and
`PadicSupercuspidal.isUnitaryBasisPairEpsilonFactor_of_generator`: on two
generators, the virtual epsilon relations of 3.8 (b) reduce to the actual
arithmetic relation and the actual basis relation. The multiplicity-weighted
product and sum over single-point supports are the values at the two classes.

`extensionMap_components`: for a class `σ` of rank `n`, a stable decomposition
written in rank `n`: `σ` is the twist of `σ₀` by the unramified character with
value `z`, the extension of `σ` is the `fieldUnramified z`-twist of `π₀`, and
the generator of `π₀` is a stable image of `σ₀`. The ranks are identified with
`extensionBasis_rank` and `Sigma.mk.inj`.

## Compatibility

`extensionMap_pairFactors`: given candidate existence and stable images in every
rank with local constants in the Weil carrier universe, the GL-side epsilon
twist statement and `ArithmeticPairUnramifiedTwistStatement` (module
`HenniartExtensionInputs`), the extension satisfies the published
`SupercuspidalPairFactorCompatibility` for every local-constant system
`(eC, ε, hε)`.

Proof. For `σ` of rank `r + 1` and `τ` of rank `n + 1`, take decompositions with
`σ₀, π₀, z` and `τ₀, ρ₀, z'`, and a common candidate `Φ` for `σ₀` and `τ₀`
(`exists_common_candidate₂`). The pair-factor clause of 3.8 (b) for `ψ` supplies
a self-dual measure. For each self-dual `ν` it gives:

- a JPSS L-polynomial `P` of `(π₀, ρ₀)` with arithmetic L-factor `1 / P` of
  `(σ₀, τ₀)` (published `isUnitaryPairLFactor_generator_iff` and
  `unitaryPairLFactor_generator`). Twisting gives `P(z z' X)` on both sides.
- for the supplied system, a common epsilon certificate `(c, m)` of `(σ₀, τ₀)`
  and `(π₀, ρ₀)`. Twisting gives `(c (z z') ^ m, m)` on both sides.
