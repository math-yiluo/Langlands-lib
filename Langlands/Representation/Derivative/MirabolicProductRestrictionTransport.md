# Transport of compact induction along a topological group isomorphism

Author: Worker 1163.

This helper module of the proof of
`Langlands.Derivative.MirabolicProductRestrictionStatement` proves the elementary
transport of the published compact induction `Induction.compactInduced` along an
isomorphism of the ambient groups, with a change of coefficient space. It is a
general internal lemma with no separate literature source.

## Data

`φ : H ≃ₜ* H'` is an isomorphism of topological groups (both topological
groups), `S ≤ H` and `S' ≤ H'` are subgroups with `h ∈ S ↔ φ h ∈ S'` (`hS`),
`τ` and `τ'` are representations of `S` on `V` and of `S'` on `V'`, and
`E : V ≃ₗ V'` satisfies `E (τ s v) = τ' (φ s) (E v)` for all `s ∈ S` (`hE`). No
smoothness of `τ`, `τ'` is assumed.

## Declarations

In namespace `Langlands.Induction`:

- `transportQuotient φ S S' hS : S' \ H' → S \ H` is induced by `φ⁻¹`, and it is
  continuous (`continuous_transportQuotient`).
- `transportFunction` sends a compactly supported covariant function `f'` for
  `(S', τ')` to `h ↦ E⁻¹ (f' (φ h))`. Covariance follows from that of `f'` and
  `hE`; right invariance under the open subgroup `φ⁻¹ K'` follows from that of
  `f'` under `K'`; and its projected support is the image of the projected
  support of `f'` under `transportQuotient`, hence compact.
- `compactInducedTransport φ S S' hS τ τ' E hE` is the resulting equivalence of
  representations of `H` from `(compactInduced S' τ') ∘ φ` to
  `compactInduced S τ`; the inverse is the same construction for `φ⁻¹`, `E⁻¹`,
  and the intertwining property is `φ (x g) = φ x φ g`.
- `eval_compactInducedTransport`: its values are `E⁻¹ (f' (φ h))`.
- `compactInducedTransport_natural`: for coefficient intertwiners `T : τ → τ₂`,
  `T' : τ' → τ₂'` compatible with `E` and `E₂`, the transport commutes with the
  published `compactInducedMap`.

## Imports

Only `Langlands.Representation.Induction.Definitions` (the published compact
induction and its constructors `compactFunctionOf`, `compactInducedMap`).
