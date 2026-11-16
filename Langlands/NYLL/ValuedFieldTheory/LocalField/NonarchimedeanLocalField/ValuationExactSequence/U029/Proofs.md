# NYLL M134.029: integer units are exactly the valuation kernel

The paired Lean file proves exactly
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zeroStatement.{u}`
under the required name
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero`.
The statement and every imported file remain unchanged.

The theorem has one arbitrary universe `u`. The target is a closed
proposition universally quantifying `(K : Type u)`, `[Field K]`,
`[ValuativeRel K]`, `[TopologicalSpace K]`,
`[IsNonarchimedeanLocalField K]`, and `(x : Kˣ)`, in this order.
Its conclusion is

```lean
x ∈ MonoidHom.range (integerUnitsToFieldUnits K) ↔
  valuationMap K (Additive.ofMul x) = 0
```

The inclusion is the actual map from valuation-ring units to field units,
and the valuation is the actual normalized additive integer valuation.
The statement adds no normalization or choice of uniformizer.

## Implemented proof and dependencies

After introducing all target binders, the proof follows the original
`constructor` argument unchanged. In the forward implication, take a
valuation-ring unit `u` representing `x`, rewrite by `valuationMap_apply`
(M134.004), and use `v_integerUnitsToFieldUnits` (M128.019). In the reverse
implication, a field unit of valuation zero has the constructed preimage
`integerUnitOfValuationMapZero K x hx` (M134.027). The published
`integerUnitOfValuationMapZero_spec K x hx` (M134.028) proves that its image
is `x`. No specification lemma is copied or redeclared.

The direct imports are the published target module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements`
and the following published proof modules:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U028.Proofs`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs`.

The U028 import also supplies the existing reconstructed-unit definition
through its dependencies. No helper theorem, instance or new data is added.
The proof retains the full arbitrary-universe scope and all source binder
kinds and order.

## Source correspondence and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
M134.029: docstring at line 282, complete theorem type at lines 283–287,
proof at lines 288–295. The file SHA-256 is
`8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`.
The original is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public port inventory records no patch10 change for this module;
no applicable NYLL erratum was found in the available errata notes.

Worker 290 extracted only M134.029, prefixed the namespace with
`Langlands.NYLL`, replaced the broad source imports by the focused published
modules above, and wrote the theorem type as its exact closed proposition.
The initial `intro` unfolds the proposition and introduces the source
parameters; the remaining proof is the original. The unused source
noncomputable section and other source declarations are omitted. The
original theorem had no simp attribute, and none is added.

## Attribution and scope

The original copyright, Apache-2.0 release and author header are retained.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply,
with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This unit proves the specified valuation-kernel support theorem and
discharges no host class-formation, cup, transfer, Tate or reciprocity target.
