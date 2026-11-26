# Vanishing of an inner exponent component with unitary outer restriction

`AdelicNestedUnitaryRestrictionVanishingStatement` uses equality of the half moduli on common
positive split points and the following nested decompositions. For `Q ≤ P ≤ R`, let `f` be automorphic on the `R` parabolic quotient. Suppose `C_P f` and
`C_Q f` have finite normalized exponent decompositions and the terms of `C_P f` have finite
`Q` decompositions after taking their `Q` constant terms. If the weak term of `f` along `P`
vanishes, every normalized `Q` exponent whose restriction to the positive split component of
`P` is unitary has zero component. The unitary restriction is expressed by norm one at all
positive split points with the same image in `G(𝔸)`.

The nested exponent comparison identifies the raw character values at those common points.
Equality of the half moduli therefore identifies the normalized values. A nonzero `Q`
component with the given restriction can only come from a unitary `P` component. Directness
of the finite exponent sum forces each such `P` component to vanish. Ordinary transitivity on
the parabolic quotient and linearity regroup the nested `Q` decompositions into an expansion of
`C_Q f`. Directness compares the selected `Q` label with the original expansion, hence that
component is zero.

The theorem `adelicNestedUnitaryRestrictionVanishing` isolates the exponent comparison in the first paragraph of the proof of Delorme,
*On the spectral theorem of Langlands* (2023), Lemma 3.10 (i), pp. 15–16. The criterion that
relates strict exponent inequalities to square integrability is a separate result.
The locator uses `Delorme--On the spectral theorem of Langlands--2023.pdf`, file SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, registered under
`delorme-2023-spectral-theorem-langlands`.
