# Shared induced character expansions from the induced character formulas

`SharedInducedCharacterExpansionFormulaReductionStatement.{u, v, uV, uW}` says
that `InducedCharacterFormulaStatement.{u, uV}` and
`TwistedInducedCharacterFormulaStatement.{u, v, uW}` together imply the
Library's `SharedInducedCharacterExpansionStatement.{u, v, uV, uW}`. That
statement is the expansion premise of `sigmaLiftInductionReduction`, the
Library's conditional proof of `SigmaLiftInductionStatement` (Henniart–Lemaire
2011, II.4.4–II.4.5). `sharedInducedCharacterExpansion_of_formulas` proves the
implication for all four universes. It does not prove either formula.

`leviTensorIntertwiner_toLinearMap` records that the linear map of
`A₁ ⊗ ⋯ ⊗ A_r` is `PiTensorProduct.map` of the linear maps of the `A i`
(definitional).

## Proof implemented in Lean

Let `δ` be norm associated with a regular semisimple `γ`.

1. `exists_isLeviClassSystem` gives a Levi class system `m : Fin k → B.Levi F`
   for `γ`.
2. For each `j`, take `x` with `x⁻¹ γ x = leviEmbedding (m j)`. Then `δ` is norm
   associated with `leviEmbedding (m j)` (`IsNormAssociated.twistedConj`), and
   `leviEmbedding (m j)` is regular semisimple (`isRegularSemisimple_conj`).
   The Library's `regularLeviNormRepresentative` gives a σ-conjugate
   `leviEmbedding (d j)` of `δ` in the Levi with `N(d j i) = m j i` exactly for
   each block. It also shows that every block `m j i` is regular semisimple.
3. The shared expansion uses the data `d`, `m` and the weights
   `w j = relativeDiscriminantWeight B (m j)`. Exact block norms give block
   norm association with the identity conjugator.
4. Ordinary part. Given block character values `a j i` of the `π i` at
   `m j i`, the external tensor theorem `hasTwistedCharacterValue_external`,
   with identity twists (`PiTensorProduct.map_id` and
   `hasTwistedCharacterValue_one_iff`), gives the Levi character value
   `∏ i, a j i` at `m j`. The ordinary formula then gives
   `∑ j, w j * ∏ i, a j i` at `γ`.
5. Twisted part. Given block twisted values `b j i` of the `P i` at `d j i`, the
   same theorem gives the Levi twisted value `∏ i, b j i` at `d j` for
   `A₁ ⊗ ⋯ ⊗ A_r`. The twisted formula, applied with the representatives of
   step 2, gives `∑ j, w j * ∏ i, b j i` at `δ`.

The topological instances on the block groups and on the Levi are the
`LocalFieldTopology` certificates. Second countability of `GL_{n_i}`, needed by
the external tensor theorem, is `generalLinear_secondCountableTopology`.
