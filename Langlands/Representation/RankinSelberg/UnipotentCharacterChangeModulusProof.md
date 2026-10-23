# Unipotent Haar character-change conjugation modulus

Author: Worker 318.

The theorem `Langlands.RankinSelberg.unipotentCharacterChangeModulus` has exactly
the type `Langlands.RankinSelberg.UnipotentCharacterChangeModulusStatement.{uF}`.
It proves the published statement without any additional hypothesis, for every
field-carrier universe, prime `p`, `F : PadicField p`, topological realization
`T`, natural number `n`, and unit `a : F.Carrierˣ`.

For the actual integral-normalized Haar measure `μ = unipotentHaar F.Carrier n`
on `upperUnipotent (n + 1) F.Carrier`, the conclusion is

```text
Measure.map (characterChangeConj a n) μ
  = (characterChangeModulus (normalizedAbsoluteValue T) a n : ℝ≥0∞)⁻¹ • μ.
```

The statement's supplied topology, valuative relation, local-field structure,
and Borel measurable structure are retained. No published file is modified.

## Implemented proof

The proof installs the singleton shape `B = singletons (n + 1)` and the Borel
structure on its actual unipotent radical. The published
`T.unipotentRadicalTopologicalGroup B` supplies its topological group structure.
Let `e = upperUnipotentContinuousEquivRadical F.Carrier`, the continuous group
equivalence from the upper-unipotent subgroup to that radical. Mathlib's
`ContinuousMulEquiv.isHaarMeasure_map`, together with the existing
`unipotentHaar_isHaar` instance, makes `μ.map e` a Haar measure on the radical.
Its normalization need not be identified separately: the block theorem applies
to every Borel Haar measure.

Apply the published proof `Langlands.glBlockModulusHaar` to this pushed-forward
measure and to `characterChangeLevi a n`. The result has inverse scalar
`(T.leviModulus B (characterChangeLevi a n) : ℝ≥0)⁻¹`.
The published `leviModulus_characterChangeLevi` rewrites its base to
`characterChangeModulus (normalizedAbsoluteValue T) a n`.

The identity `upperUnipotentEquivRadical_characterChangeConj` states that
`e ∘ characterChangeConj a n` equals the Levi action composed with `e`.
Continuity of `e`, `measurable_characterChangeConj`, and
`BlockShape.continuous_leviAction` give measurability of the three maps.
`Measure.map_map` therefore transports the block equality through this
intertwining, and `Measure.map_smul` moves the scalar through pushforward.
Since `e` is a homeomorphism of Borel spaces, it is a measurable embedding;
`MeasurableEmbedding.map_injective` then recovers equality of the original
measures on the upper-unipotent group.

Finally, `characterChangeModulus_ne_zero` allows `ENNReal.coe_inv` to identify
the coercion of the inverse nonnegative real scalar with the inverse of its
coercion. The nonnegative-real action on measures agrees definitionally with
the action through this coercion. This yields the exact scalar in the target.
The reciprocal is preserved throughout, as required for a pushforward, which
evaluates preimages.

There is no positive-rank or nonempty-coordinate assumption. In particular,
`n = 0` is included by the same proof. The only new declaration is the closing
theorem; the equivalence, Haar measure, measurability facts, intertwining, and
specialized block identity used above are local proof bindings.

## Provenance

This is an internal transport proof of the existing Library statement. It
imports `UnipotentCharacterChangeModulusStatement`,
`CharacterChangeSingletonBlocks`, and `BlockModulusHaarProof` by their Lean
module names. The first supplies the target and measurability helper, the
second supplies the singleton identification, conjugation identity, and modulus
identity, and the third supplies the unconditional block Haar theorem.
The proof assumes no Jacobian, coordinate measure formula, Haar uniqueness law,
or unproved proposition. It uses the established proofs of the imported results
and Mathlib's pushforward facts, and asserts no new literature result.
