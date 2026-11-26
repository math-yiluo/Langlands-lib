# Weak constant-term transitivity from nested exponent decompositions

`StandardNestedHalfModulusCompatibilityStatement` states the comparison of the two half
moduli along nested standard parabolics `Q ≤ P`. If a point of the positive split component
of `P` and a point of the positive split component of `Q` have the same image in `G(𝔸)`, their
half-modulus values for `P` and `Q` agree. In Delorme's normalization the contribution of
`Q ∩ M_P` to the modulus ratio is trivial on the split component of `P`, which is central in
`M_P`. The comparison is taken as a premise in this module.

`exists_automorphicExponentDecomposition_sum` groups a finite family of decompositions by
normalized label. Its support is the union of the individual supports, and each new
component is the sum of the terms with that label. These sums retain automorphy and the
polynomial orbit condition. Filtering their labels by zero real part commutes with summing
over the original family.

`isWeakConstantTerm_of_nested_decompositions` assumes the half-modulus comparison and a
`Q`-decomposition for the `Q` constant term of each component of a given `P`-decomposition of
`Φ_P`. By ordinary transitivity and linearity, summing the `Q`-decompositions of all components
gives a decomposition of `Φ_Q`. Summing only over the unitary `P` labels gives one for
`(Φ_P^w)_Q`. The nested exponent comparison gives a zero unitary sum for each nonunitary
`P` label, so the two weak sums agree. Uniqueness identifies this sum with any specified
weak term of `Φ` along `Q`. The existence of the component decompositions is an input.

Source. P. Delorme, *On the spectral theorem of Langlands*, published PDF in the registered
`delorme-2023-spectral-theorem-langlands` collection, SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`. See (3.2) on p.10 and the
normalizations (3.5)–(3.6) and Lemma 3.8 (iii) on p.14.
