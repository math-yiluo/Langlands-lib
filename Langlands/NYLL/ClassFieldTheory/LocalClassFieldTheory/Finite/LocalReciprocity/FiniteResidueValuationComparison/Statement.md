# Finite-separable comparison of restricted valuation rings: statement

The module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueValuationComparison.Statement`
defines the closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ValuationSubring.restrictIntermediateField_eq_of_finite_separableStatement`.
It states exactly the theorem M251.001 of Naganori Yamaguchi's
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueValuationComparison.lean`, lines 33–59](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueValuationComparison.lean#L33-L59).
The complete original file has SHA-256
`3bccfb4b9d1259718ed253339c34d5d5e80b6266c627ad9d5cf90512a4633c90`.
I read the whole original file (62 lines). It contains:

- the namespace `LocalClassFieldTheory` (line 21);
- `open ValuationTheory RamificationTheory` (23);
- `universe u v w` (29) and `open DiscreteValuationField` (31);
- the docstring (33–36), the signature (37–44) and the proof (45–59).

This unit states the proposition and does not prove it. The proof is a
separate proof unit, under the adapted source name
`Langlands.NYLL.LocalClassFieldTheory.ValuationSubring.restrictIntermediateField_eq_of_finite_separable`.

## Exact proposition and binder kinds

The declaration has type `Prop`, with universe parameters `u, v, w` and no
parameters outside its body. Its entire body, written inside
`namespace Langlands.NYLL.LocalClassFieldTheory` under
`open ValuationTheory RamificationTheory` and `open DiscreteValuationField`,
is:

```lean
∀ {K : Type u} {Omega : Type v} [Field K] [Field Omega] [Algebra K Omega]
  (base : CompleteDVF.{u, w} K)
  (A : _root_.ValuationSubring Omega)
  [_root_.Valuation.HasExtension base.valuation A.valuation]
  (E : IntermediateField K Omega) [FiniteDimensional K E]
  [Algebra.IsSeparable K E]
  (C : _root_.ValuationSubring E)
  [_root_.Valuation.HasExtension base.valuation C.valuation],
  A.restrictIntermediateField E = C
```

The names resolve as follows:

- `CompleteDVF` is the Library's existing
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`. No new
  copy is made. A `CompleteDVF.{u, w} K` is a structure on the field `K`. It
  bundles a value group `base.ValueGroup : Type w`, a valuation
  `base.valuation : Valuation K base.ValueGroup`, and a proof that this
  valuation is complete and discrete of rank one (in particular nontrivial).
- `A.restrictIntermediateField E` is the published M233.004 definition
  `Langlands.NYLL.RamificationTheory.ValuationSubring.restrictIntermediateField`,
  applied to `A` and `E` by dot notation. It is the preimage of `A` under the
  inclusion `E → Omega`.
- `Valuation.HasExtension`, `FiniteDimensional`, `Algebra.IsSeparable`,
  `IntermediateField` and `ValuationSubring` are Mathlib's.
  `A.valuation` and `C.valuation` are the canonical valuations of the
  valuation subrings.

The binder kinds are those of the source:

- `K` and `Omega` are implicit;
- `base`, `A`, `E` and `C` are explicit;
- the field and algebra structures, both extension hypotheses, finite
  dimensionality and separability are instance binders.

The universes are those of the source: `u` for `K`, `v` for `Omega`, and `w`
for the value group of `base`. In the source, `CompleteDVF K` leaves that
last universe implicit, and Lean auto-binds it as a fresh universe
parameter. Here it is named `w`. The source's declared `w` (line 29) does not
occur in the theorem.

## Meaning

Take a complete discretely valued field `K`. Take a valuation subring `A` of
an extension field `Omega` whose valuation extends that of `K`. Take a finite
separable intermediate field `K ⊆ E ⊆ Omega` and any valuation subring `C` of
`E` whose valuation also extends that of `K`. Then the restriction
`A ∩ E` of `A` to `E` equals `C`. In other words, over a complete DVF, a
finite separable extension has only one valuation subring extending the base
valuation, and the restriction of `A` is it.

`Omega` is an arbitrary field extension of `K` with no algebraicity
assumption. The proposition adds no hypothesis beyond the source's: in
particular no residue-field, Galois or local-field condition.

## Source correspondence and modifications

| Source item | Adapted item |
| --- | --- |
| `namespace LocalClassFieldTheory` (21) | `namespace Langlands.NYLL.LocalClassFieldTheory` |
| `open ValuationTheory RamificationTheory` (23), `open DiscreteValuationField` (31) | The same `open` commands, which resolve to the `Langlands.NYLL` namespaces |
| `universe u v w` (29) and the auto-bound value-group universe | The explicit universe parameters `.{u, v, w}`, with `w` the value-group universe |
| Signature of M251.001 (37–44) | The body of `ValuationSubring.restrictIntermediateField_eq_of_finite_separableStatement` |
| Proof (45–59) | Deferred to the separate proof unit |

Other modifications:

- **Closed proposition.** The universal closure inside the proposition is an
  organizational adaptation of the source theorem signature, not a new
  assertion. Its content is exactly the source statement.
- **Names.** Mathlib's `ValuationSubring` and `Valuation.HasExtension` are
  written with `_root_`. The source writes them with dot notation and
  unqualified names, which resolve to the same Mathlib declarations.
- **Section.** The source's `noncomputable section` is unnecessary for a Prop
  definition and is omitted.
- **Imports.** The two upstream imports are replaced by:
  - the published `CompleteDVF` module
    `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`;
  - the published M233.004 module
    `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.RestrictIntermediateField`;
  - `Mathlib.FieldTheory.Separable`, `Mathlib.LinearAlgebra.FiniteDimensional.Defs`
    and `Mathlib.RingTheory.Valuation.Extension`.

The source proof goes through M245.018 and M196.039
`target_valuationSubring_eq_of_finite_separable`. That proof route does not
affect this statement. The proof unit replaces the M196.039 step and records
the replacement. Searches of Mathlib and the Library found no existing
declaration for this statement.

## Attribution

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the original path
above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
public port partition `notes/reuse/nyll-public-port/m241-m258.md` lists
M251.001 and records no patch10 change for this source module. The workspace
`notes/errata` directory has no entry for this source. The NYLL NOTICE does
not list this source file among its third-party paths.

Original copyright and authorship are kept: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by
OpenAI Codex). Apache-2.0 applies. The existing verbatim
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean header records the modifications, made by Worker 122 on
13 November 2026. The approved environment is Lean 4.34.0 with Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. Upstream used Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
