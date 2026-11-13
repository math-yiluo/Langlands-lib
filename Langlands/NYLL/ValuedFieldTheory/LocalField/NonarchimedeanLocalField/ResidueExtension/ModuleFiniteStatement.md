# Module finiteness of integer rings from integral closure

The Prop-valued definition
`Langlands.NYLL.LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosureStatement`
records NYLL M138.026. In a finite separable extension of a
nonarchimedean local field, if the extension valuation ring is the integral
closure of the base valuation ring, the two actual integer rings form a
finite module extension. This contribution publishes the exact target,
without a proof of that target.

## Pinned source and name map

Naganori Yamaguchi,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`,
lines 333–343](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L333-L343),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`.
The docstring occupies lines 333–335, the theorem starts on line 336,
its signature ends on line 342, and the proof is on line 343.

The original
`LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosure`
becomes
`Langlands.NYLL.LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosureStatement`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable checkout is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The public inventory is `notes/reuse/nyll-public-port/m121-m144.md`,
M138.026. Source lines 1–100 and 333–343 were read.

## Exact telescope and proposition

The sole universe is the source `u`. All parameters retain their original
binder kinds and order:

```lean
(K L : Type u)
[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
[Algebra.IsSeparable K L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

The definition returns `Prop`, with body exactly
`Module.Finite 𝒪[K] 𝒪[L]`.

The notation `𝒪[K]` and `𝒪[L]` means the actual integer subrings of the
supplied `ValuativeRel` valuations. The scalar structure on `𝒪[L]` is the
canonical restriction of the supplied `Algebra K L`, provided by Mathlib's
`Valuation.HasExtension.instAlgebraInteger`. The integral-closure hypothesis
uses these rings and their canonical inclusions into `L`; it identifies the
image of `𝒪[L]` with the elements of `L` integral over `𝒪[K]`.

Only `K` carries the source topology and
`IsNonarchimedeanLocalField` assumption. No topology or local-field instance
on `L` is added. `FiniteDimensional K L`, separability, valuation extension
and the actual integral-closure identification remain hypotheses. The
conclusion asserts finiteness over the integer ring, rather than the
already assumed finite-dimensionality over the field.

## Modifications and imports

Worker 252, 13 November 2026:

- prefixed the namespace with `Langlands.NYLL` and appended `Statement`;
- changed the theorem into a `def` returning `Prop`, keeping the source
  universe, complete telescope, docstring and conclusion;
- omitted the proof term `IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]`;
- extracted only M138.026 and replaced the original module documentation;
- reduced imports to the Mathlib modules listed below.

| Import | Purpose |
| --- | --- |
| `Mathlib.FieldTheory.Separable` | `Algebra.IsSeparable` and field-extension infrastructure |
| `Mathlib.NumberTheory.LocalField.Basic` | `IsNonarchimedeanLocalField`, valuation integer rings and scoped notation |
| `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic` | `IsIntegralClosure` |
| `Mathlib.RingTheory.Valuation.Extension` | `Valuation.HasExtension` and the canonical integer-ring algebra |

No preceding NYLL declaration of `ResidueExtension` is required by this
signature, and no additional instance is installed. The original theorem's
proof uses Mathlib's `IsIntegralClosure.finite`; that possible later proof
route does not constitute a proof publication here.

## License

The original copyright and author header is preserved. The upstream
Apache-2.0 license and notice remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
compiled this module with zero errors and warnings and inspected the named
definition with `statement_returns_prop: true`, level parameters `[u]`, and
only `propext`, `Classical.choice` and `Quot.sound`. This development check
does not establish independent acceptance, publication or a target proof.
