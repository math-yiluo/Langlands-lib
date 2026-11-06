# Archimedean components for the Harris datum characters

Worker 84. Helper lemmas in namespace `Langlands.Global.HarrisDatum` for the
archimedean conditions of `Harris.IsProposition48Datum`. They are used by
`HarrisDatumCharacterRealizationProof`. Every result is proved; nothing is
assumed.

## Components at one place

- `single v y` is the archimedean idele equal to `y` at the place `v` and to
  `1` elsewhere; it is the unit map of Mathlib's
  `InfiniteAdeleRing.ofCompletion v`.
- `infiniteComponent_eq_atInfinity`: the component of a Hecke character at
  `v` is its archimedean part evaluated on `single v y`.
- `toCharacter_single`: the infinity character of an integral type `a` takes
  `single v y` to `z^{a σ} z̄^{a σ̄}`, where `z` is the image of `y` under
  `extensionEmbedding v` and `σ = v.embedding`.

## Reading components on the base

For an extension `E'/E`, a place `τ` of `E` and a place `w` of `E'` above it,
`lift τ w` is `w.embedding` when it restricts to `τ.embedding`, and its
conjugate otherwise. It restricts to `τ.embedding` (`lift_comp`) and defines
`w` (`mk_lift`). By Mathlib's `liesOver_extensionEmbedding` and its conjugate
form, `extensionEmbedding w` after `LiesOver.completionMap` is
`extensionEmbedding τ` or its conjugate, according to the two cases.

- `infiniteComponent_completionMap`: if `χ` has prescribed infinity type
  `A`, then its component at `w`, read on `E_τˣ` through the completion map,
  is `z ↦ z^{A ŝ} z̄^{A ŝ̄}` with `ŝ = lift τ w`.
- `infiniteComponent_completionMap_twist`: the same formula with the factor
  `|z|`, for a character whose archimedean part times `∏ |z_v|` is the
  infinity character of a type `t`.

## Relative regularity

`isRelativelyRegular_of_weights` proves `Harris.IsRelativelyRegular E (X * Y)`
under three hypotheses: `X` has an anticyclotomic prescribed type `A`; `Y` has
the same component, read on `E_τ`, at all places above `τ`; and
`A (lift τ w) ≠ A (lift τ w')` for distinct places `w`, `w'` above `τ`. If
the components at `w` and `w'` agree at `x ∈ E_τˣ`, cancelling the `Y` factor
gives `(z/z̄)^k = 1` with `k = A (lift τ w) − A (lift τ w') ≠ 0`. The proof
takes `z = exp(iπ/(2k))`, for which `(z/z̄)^k = −1`, and uses surjectivity of
`extensionEmbedding τ` at a complex place.

## Weights above an imaginary quadratic field

For a field `K₀` with `[K₀ : ℚ] = 2` that is totally complex:

- `eq_or_eq_conjugate`: every embedding is `τK` or `τ̄K`, because there are
  two embeddings and `τK ≠ τ̄K`.
- `regularWeights j τK` is `σ ↦ g σ + 1` on embeddings of `E'` over `τK` along
  `K₀ → E → E'`, and `σ ↦ −(g σ̄ + 1)` on the others, for an enumeration `g`.
  It is anticyclotomic (`regularWeights_anticyclotomic`) and has distinct
  weights above `τK` (`regularWeights_distinct`).
- `halfWeights j τK` is `1` on embeddings over `τK` and `0` on the others. It
  is pure of weight one (`halfWeights_pure`).
- `weights_ne_of_distinct`: distinct weights above `τK` separate `lift τ w`
  and `lift τ w'` for distinct `w`, `w'` above any `τ`. When `τ` restricts to
  `τ̄K` on `K₀`, the proof passes to conjugates.
- `halfWeight_component_eq`: a character realizing `halfWeights` has equal
  components, read on `E_τ`, at all places above `τ`.

## Parity and conjugation

- `toCharacter_add`, `atInfinity_mul`.
- `isAlgebraicAfterTwist_zero_of_type` and `isAlgebraicAfterTwist_one_of_types`
  give `Harris.IsAlgebraicAfterTwist 0 X` and `Harris.IsAlgebraicAfterTwist 1 (X * ψ)`.
- `isAlgebraicAfterTwist_of_mod_two` reduces `IsAlgebraicAfterTwist k` to
  `k % 2` with the published `Harris.isAlgebraicAfterTwist_add_two_iff`.
- `isConjugateInverse_mul`: products of conjugate-inverse characters are
  conjugate-inverse.

`HarrisDatum.toCharacter_add` reuses the identical `Harris.toCharacter_add` theorem from `HarrisSetup`.
