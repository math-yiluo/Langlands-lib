# Exponent terms of nested twists and of convergent Eisenstein series

Module `Langlands.Global.AdelicEisensteinFarRegionTerms`, for a standard family `fam`.

## `hasUnnormalizedExponent_parameterTwist_of_le`

Let `J ≤ Q`, let `K` be Iwasawa for `P_Q`, and let `μ ∈ X^*(P_Q) ⊗ ℂ`. If `φ` has
unnormalized exponent `λ` along `J`, then the twist `φ · m_Q^μ` has exponent
`λ + res μ` along `J`. Here `res` is `parameterRestrict` along `nestedParabolicHom`. For
`x ∈ 𝔄_J`, the point `x` is the image of a point of `P_Q(𝔸)` under `nestedParabolicHom`
(`map_comp_apply_of_hom`). The height law `height_map_mul` and
`parameterPower_parameterRestrict` give `m_Q(x g)^μ = x^{res μ} m_Q(g)^μ`. The polynomial
orbit formula of `φ` is then multiplied by the constant `m_Q(g)^μ`. This extends
`hasUnnormalizedExponent_parameterTwist`, which twists along `J` itself.

## `exists_identityWeyl_support`

This theorem assumes `ConvergentCuspidalTestExpansionStatement`, a compact `K` in good
position that is Iwasawa for `P_Q`, and finitely many `ψ i` automorphic on
`U_Q(𝔸) M_Q(F) \ G(𝔸)`. Assume also that the tests of `C_J ψ i` converge when `J ≤ Q`. For
a standard `J` it gives one threshold `R` and, for each `i`, competing Weyl data for the
identity Weyl element of `(Q, J)`. Let `μ` be `R`-regular, and suppose every `E(ψ i, μ)` is
automorphic with convergent tests of `C_J E(ψ i, μ)`. Then for every coefficient vector `a`
and every Levi cusp form, the following scalar test is supported in the characters of the
labels `(data i).label j μ`:

`g ↦ (C_J (∑ i, a i · E(ψ i, μ)) (· g), ψ) − (C_{Q,J}(∑ i, a i · ψ i)_μ (· g), ψ)`.

The proof applies the expansion statement to each `ψ i` with the identity normalizer
point (`isWeylConjugation_one`). The identity intertwining integral is the twist
(`IsIwasawaCompact.intertwiningIntegral_one_self`). The threshold is `∑ i, |R i|`. The
constant terms and pairings are linear in the finitely many inducing functions
(`leviPairing_constantTerm_sum_smul`, `leviPairing_parabolicConstantTerm_twist_sum_smul`).
Each competing term lies in the eigenspace of its label. The identity-element case is
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), (6.21),
used in Proposition 6.9. Taking all `ψ i` at once gives one threshold for all coefficient
vectors, which the far-region step needs because the coefficients vary with the parameter.
