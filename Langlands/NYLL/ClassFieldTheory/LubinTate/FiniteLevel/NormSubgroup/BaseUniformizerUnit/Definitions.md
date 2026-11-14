# The chosen base uniformizer as a field unit

This module extracts exactly M374.002, lines 44–49 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/NormSubgroup.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/NormSubgroup.lean#L44-L49)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file's SHA-256 is
`316f65ec1b8cae536827f3ff3426829bf3173bfa0ce631bfb0cb081958470467`.
Its full contents, including the universe and section context and the adjacent
coercion lemma, were read directly from the registered pinned snapshot.
The source registrations are `external-lean-reuse-snapshots-2026-10-21`
and `nyll-classfieldtheory-fbd320cd-supplement`.
The project errata lookup contained no matching entry. The port inventory
records no patch10 change to this source module.

## Definition and exact source correspondence

The original `LubinTate.standardLubinTateBaseUniformizerUnit` becomes
`Langlands.NYLL.LubinTate.standardLubinTateBaseUniformizerUnit`.
Its complete signature is:

```lean
{K : Type u} [Field K]
{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}
{π : F.valuationSubring}
(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) : Kˣ
```

The universes `u` and `v` remain independent. The field, field instance,
chosen local-field package and element of its valuation subring are implicit;
the uniformizer proof is explicit. The body remains exactly
`Units.mk0 (π : K) hπ.ne_zero`.
Thus the definition regards the supplied uniformizer as a unit of the field.
It retains the chosen valuation through `F` and its uniformizer hypothesis.
It does not assert that the uniformizer is a unit of the valuation subring.
The inverse stored by `Units.mk0` is the field inverse of `(π : K)`.

## Reused declarations and focused import

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`.
It supplies the actual published FM package
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`
and its `toCompleteDVF` parent projection and `valuationSubring`
abbreviation. The parent retains its chosen value group and valuation.
This definition reuses those declarations, the inherited
`CompleteDVF.valuation` projection, the canonical valuation-subring coercion
to `K`, and the canonical Mathlib unit group `Units K`.

Mathlib's `Valuation.IsUniformizer.ne_zero` supplies the proof
`hπ.ne_zero : (π : K) ≠ 0`. Mathlib's `Units.mk0` constructs the field unit
with that value and its field inverse. These are existing declarations, also
available through the sole import; there is no new valuation, local-field
structure or instance.

The upstream imports of `NormUniformizer` and `NormQuotient` are unnecessary
for this definition. The earlier source definition M374.001 and the level-field
construction are likewise unnecessary. The focused module contains exactly
one data definition, with no theorem or proposition target.

## Coercion correspondence for the dependent route

M374.003 is the adjacent source lemma
`LubinTate.standardLubinTateBaseUniformizerUnit_coe`, lines 54–58, with its
`@[simp]` attribute at line 53. After qualification, its claimed equality is:

```lean
(Langlands.NYLL.LubinTate.standardLubinTateBaseUniformizerUnit hπ : K) = (π : K)
```

Unfolding the definition and `Units.mk0`, coercion from `Kˣ` projects its
stored value `(π : K)`, so this equality is definitionally reflexive.
The focused private development probe checks this exact equality by `rfl`
with the full source telescope and independent universes. It also checks
the entire definition against the displayed signature and body by reflexivity.
These checks document the dependent route; M374.003 is not declared or
published in this module. No other source unit is extracted.

The focused development check compiled this definition and both private
reflexivity examples on 14 November 2026 with zero errors and warnings.
Declaration inspection confirmed kind `definition` and level parameters
`["u", "v"]`. The check used environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for `NormSubgroup.lean`.

Worker 330 made these modifications on 14 November 2026:

- extracted only M374.002 and its docstring into this focused module;
- prefixed the declaration namespace and opened local-field namespace
  with `Langlands.NYLL`;
- replaced the two upstream imports with the one published import above;
- omitted the redundant outer `noncomputable section` and its closing `end`,
  retaining the declaration's explicit `noncomputable` modifier;
- replaced the module documentation, added the prominent modification
  record in the Lean header, and wrote this paired Markdown.

The definition's universes, parameter order, binder kinds, mathematical type
and body are unchanged apart from namespace qualification. The external
repository is neither imported nor installed.
