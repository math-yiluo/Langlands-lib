# The Galois twist of upper adelic points

Helper module for the proof of `GaloisBorelTwistingStatement` (Task 5268).

Let `G` be an affine group over a number field `F`, `L/F` finite, `W = R_{L/F}(G_L)` the Weil
restriction of the base change. The upper adelic points `G_L(𝔸_L)` are identified with
`W(𝔸_F)` (`weilAdelicEquiv`, a Library homeomorphism) and with `G(L ⊗_F 𝔸_F)`
(`tensorAdelicEquiv`, with coordinate formula `tensorAdelicEquiv_apply`).

`galoisTwist F L G σ` is the continuous homomorphism `φ_σ` of `G_L(𝔸_L)` obtained by
transporting the action of the ground-field Galois endomorphism
`AffineWeil.unitGaloisAction σ` of `W` on `W(𝔸_F)`. In tensor coordinates it is coefficient
conjugation by `σ ⊗ 1` (`galoisTwist_tensorAdelicEquiv`).

It proves the first two clauses of `IsGaloisBorelTwist`:

- `galoisTwist_rationalSection` (clause 1): `φ_σ` acts on rational points `q ∈ G_L(L)` as
  `rationalConjugate σ`;
- `galoisTwist_scalarExtension` (clause 2): `φ_σ` fixes the image of `G(𝔸_F)^1` under the
  scalar-extension map.

Helper lemmas: `tensorLeft` (the map `G(L) → G(L ⊗ 𝔸_F)`), `conjugate_tensorLeft`,
`affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv`, `tensorAdelicEquiv_tensorLeft`,
`scalarExtensionNormOneMap_val`.
