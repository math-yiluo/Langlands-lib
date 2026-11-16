# Canonical uniformizer-principal subgroup index target (M377.004)

`Langlands.NYLL.LubinTate.standardLubinTateCanonicalUniformizerPrincipalSubgroup_indexStatement`
is a proposition definition with the complete telescope

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (n : ℕ) : Prop
```

The field `K` is explicit and lies in Type 0. The four instance arguments
occur in the displayed order, and `n` is explicit. With
`open scoped ValuativeRel` and the `Langlands.NYLL.LubinTate` and
`Langlands.NYLL.LocalFieldTheory` namespaces available, its body is exactly

```lean
(LocalFieldTheory.uniformizerPrincipalSubgroup K
    (standardLubinTateBaseUniformizerUnit
      (standardLocalFieldUniformizer_isUniformizer K))
    1 (n + 1)).index =
  (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n
```

Here `𝓀[K]` is the residue field of the canonical valuation ring supplied
by `ValuativeRel K`. Put `q = Nat.card 𝓀[K]`. The asserted index is
`(q - 1) * q ^ n`, with subtraction in the natural numbers.
The subgroup is a subgroup of `Kˣ`: its definition is the supremum of
the integer powers of the displayed field unit raised to `1` and the
image in `Kˣ` of the `(n + 1)`-st principal units of the valuation ring.
Thus the target retains exponent `1` and source level `n + 1`, including
`n = 0`.

The unit is the actual published
`Langlands.NYLL.LubinTate.standardLubinTateBaseUniformizerUnit` applied to
the actual theorem
`Langlands.NYLL.LubinTate.standardLocalFieldUniformizer_isUniformizer K`.
The theorem supplies the uniformizer property for the canonical
`standardLocalField K` package and its chosen integer-ring uniformizer;
the unit definition regards that element as a nonzero field unit.
The definition infers this actual package and element from that proof.
The target has no extra uniformizer hypothesis, alternate chosen element,
or assumed index formula.

## Source correspondence

This is M377.004 of Naganori Yamaguchi's `ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardSubgroupIndex.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardSubgroupIndex.lean#L80-L119).
The docstring is at lines 80–81, the theorem declaration and type at
lines 82–88, and the proof body at lines 89–119. Its inherited field and
instance telescope is at lines 42–43; the explicit `n` is at line 83.
The full source file, including its header, imports, namespace openings,
section telescope and adjacent declarations, was read from the pinned
local snapshot. Its SHA-256 is
`09a3021fc016de44aa5717a06d80cfa849c2ec642f9301a93538f1bb184e42b8`.

The source theorem
`LubinTate.standardLubinTateCanonicalUniformizerPrincipalSubgroup_index`
becomes the displayed
`Langlands.NYLL.LubinTate.standardLubinTateCanonicalUniformizerPrincipalSubgroup_indexStatement`.
Its conclusion is preserved literally apart from resolving the source
NYLL names in the `Langlands.NYLL` namespace. The theorem is packaged as
a `def` returning `Prop`; the original section parameters are written
directly on that definition, preserving binder kinds and order.
The original docstring is retained.

The source registrations are
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching source erratum was found in the supplied Library's
`notes/errata`, and the public port inventory records no patch10 change
to this source module.

## Imports and complete modification record

The two original Mathlib imports, `Mathlib.GroupTheory.Index` and
`Mathlib.SetTheory.Cardinal.Finite`, are retained. The four broad source
NYLL imports are replaced by these actual published modules:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.UniformizerProof`
  supplies `standardLocalFieldUniformizer_isUniformizer` and its
  canonical local-field data through its imports.
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup.BaseUniformizerUnit.Definitions`
  supplies `standardLubinTateBaseUniformizerUnit`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.UniformizerPrincipalSubgroup`
  supplies `LocalFieldTheory.uniformizerPrincipalSubgroup` and the
  principal-unit subgroup data.

The original `StandardLocalField` and `NormSubgroup` imports are thus
replaced by their focused published units. The
`UniformizerPrincipalQuotient` and `FiniteParameters` imports support
the source proof and are omitted from this statement module.
No imported Lean or Markdown pair is changed.

Worker 809 made the extraction on 16 November 2026. In addition to the
namespace, declaration name, Prop packaging and import changes above,
the unused outer `noncomputable section` and its closing `end` are
omitted. `open scoped ValuativeRel` is retained for the residue-field
notation. The duplicate `open LocalFieldTheory` is reduced to one;
the unused openings of `DiscreteValuationField`, `CompleteDVF` and
`IsNonarchimedeanLocalField` are omitted. The module documentation is
replaced, a prominent modification record is added, and this paired
Markdown is new. No mathematical parameter, hypothesis, subgroup
argument or cardinal expression is changed.

Only this focused target is declared. The source proof and all other
M377 source units are outside this contribution. In particular, this
definition states the index identity without proving it; it introduces
no axiom and assumes no proof of that identity.

## Development validation

Check `b6eeee01-b5e3-485d-bf8c-ffff9c28b4d0` on 16 November 2026 compiled
this module and inspected the exact declaration with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). It returned `ok: true`,
exit code zero, zero errors and zero warnings. Inspection reported kind
`definition`, no universe level parameters and
`statement_returns_prop: true`. Its only reported assumptions are
`propext`, `Classical.choice` and `Quot.sound`.
This development check supplies no proof of the index formula and is
separate from independent semantic acceptance and Library publication.

## Attribution and license

The original 2026 copyright, Apache-2.0 release line and author header
are retained verbatim. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in `licenses/NYLL/`.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This extraction uses the registered original source and the published
inputs by Lean name; the external repository is not installed.
