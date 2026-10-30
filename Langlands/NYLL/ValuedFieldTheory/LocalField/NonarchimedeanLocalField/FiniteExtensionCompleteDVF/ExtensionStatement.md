# Extension compatibility of the canonical complete-DVF packages: statement

This module adapts exactly M248.002,
`LocalFieldTheory.localCompleteDVFValuation_hasExtension`, from Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`, lines 57–74](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean#L57-L74),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source signature is
lines 59–67 and its proof runs through line 74.

The module contains one closed proposition,
`Langlands.NYLL.LocalFieldTheory.LocalCompleteDVFValuationHasExtensionStatement.{u,v} : Prop`.
It is a `Prop`-valued `def`. It is a statement only; this module contains no
proof, instance or other declaration.

| Original | Adapted |
| --- | --- |
| `theorem LocalFieldTheory.localCompleteDVFValuation_hasExtension` (lines 59–74) | `def Langlands.NYLL.LocalFieldTheory.LocalCompleteDVFValuationHasExtensionStatement : Prop` (signature only, closed) |

## Statement

The only declaration parameters are the two independent universe levels `u`
and `v`. The proposition quantifies, in the source order,

```
(K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
```

and concludes

```
Valuation.HasExtension (localCompleteDVF K).valuation (localCompleteDVF L).valuation
```

In words: let `K` and `L` be fields, in independent universes, with a supplied
`K`-algebra structure on `L`. Each carries its own supplied valuative relation
and supplied topology that make it a nonarchimedean local field in Mathlib's
sense (`IsNonarchimedeanLocalField`). Suppose that the canonical valuation of
`L` extends the canonical valuation of `K` along this algebra map. Then the
valuation stored in the canonical complete-DVF package of `L` extends the
valuation stored in the canonical complete-DVF package of `K`, along the same
algebra map.

`localCompleteDVF` is the published M248.001 definition
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF`. For `K : Type u` it
returns a `CompleteDVF.{u,u} K` whose value group is
`ValuativeRel.ValueGroupWithZero K` with its canonical ordered structure, and
whose valuation is the canonical valuation `ValuativeRel.valuation K`. The two
packages are formed separately for `K` and for `L`. The value group stored in
the package for `K` lives in `Type u`, and the one for `L` lives in `Type v`.
The conclusion uses the bundle projections `(localCompleteDVF K).valuation`
and `(localCompleteDVF L).valuation`, with the ordered structures
`CompleteDVF.instValueGroup` stored in the packages. The `Valuation.HasExtension`
in the conclusion is used at universe levels `{u, v, u, v}`.

### Meaning of `Valuation.HasExtension`

`Valuation.HasExtension` is Mathlib's class in
`Mathlib.RingTheory.Valuation.Extension`. For a base valuation `vR` on `R` and
a valuation `vA` on an `R`-algebra `A`, `vR.HasExtension vA` has the single
field `val_isEquiv_comap : vR.IsEquiv (vA.comap (algebraMap R A))`. Thus the base
valuation is *equivalent* to the pullback of the upstairs valuation along the
actual `algebraMap R A`: for all `x y : R`,
`vR x ≤ vR y ↔ vA (algebraMap R A x) ≤ vA (algebraMap R A y)`.
It does not require equality of values, so it allows differently normalised
valuations, and here the two value groups are different types.

In this statement the algebra map is always the supplied `algebraMap K L`,
from the `[Algebra K L]` argument, in both the premise and the conclusion.

### The premise and what is not assumed

The instance premise `Valuation.HasExtension (ValuativeRel.valuation K)
(ValuativeRel.valuation L)` concerns the canonical valuations of the supplied
valuative relations. It is essential and is retained from the source. The
statement says that canonical packaging preserves an extension relation that
already holds. It does not claim that every algebra map between local fields
is compatible with the given valuative relations, and it does not establish
the premise for any particular supplied data. It does not assume the
packaged `HasExtension` relation that it concludes.

No other hypothesis is added. In particular there is no `FiniteDimensional K L`,
`Algebra.IsSeparable K L` or normality premise. There is no continuity of the
algebra map, no `UniformSpace` or `CompleteSpace` instance, no chosen
extension valuation, no integral-closure premise and no finite integer-module
premise. Neither field is specialised to `Type 0`, to `p`-adic fields, or to
the case `K = L`.

## Source correspondence

The source theorem is

```
theorem localCompleteDVFValuation_hasExtension
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    (localCompleteDVF K).valuation.HasExtension
      (localCompleteDVF L).valuation
```

in `namespace LocalFieldTheory` (line 24) with `universe u v y` (line 30). Its
docstring is reproduced as the docstring of the adapted definition. The
adaptation makes these changes:

- The theorem's arguments are moved into a universal quantifier in the same
  order and with the same binder kinds. The result is a closed `Prop`-valued
  `def`, whose only parameters are the universe levels `u` and `v`. The source
  universe `y` belongs to a later unit of the same file and is not used.
- The source conclusion `(localCompleteDVF K).valuation.HasExtension
  (localCompleteDVF L).valuation` uses dot notation. The adaptation writes the
  same constant in prefix form,
  `_root_.Valuation.HasExtension (localCompleteDVF K).valuation
  (localCompleteDVF L).valuation`. Both elaborate to the same term.
  `_root_.Valuation` is written explicitly because the declaration lives in
  the `Langlands.NYLL` namespace.
- The name is changed from `localCompleteDVFValuation_hasExtension` to
  `LocalCompleteDVFValuationHasExtensionStatement`, and the namespace is
  prefixed with `Langlands.NYLL`.
- `localCompleteDVF` refers to the published adaptation of the source's
  M248.001 definition in the same namespace.
- The source proof is omitted. It applies `Valuation.HasExtension.ofComapInteger`
  and reduces integer membership to
  `Valuation.HasExtension.val_map_le_one_iff` for the canonical valuations.
  Proving the target is left to a separate proof task.

The source file's later units are not adapted here. These are comparison of
rings of integers with the integral closure, the finite-module theorem, chosen
extension data and its instance, and uniqueness of the extension.

## Reuse and imports

The two direct imports are:

- `Mathlib.RingTheory.Valuation.Extension`, supplying `Valuation.HasExtension`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`,
  the published M248.001 module supplying `localCompleteDVF`. Through its
  imports it also supplies `IsNonarchimedeanLocalField`, `ValuativeRel` and
  `CompleteDVF`.

The original file imports the NYLL modules `NonarchimedeanLocalField.Basic`,
`DiscreteValuationField.FiniteIntegralClosure` and `ValuedAdicComplete`, and
`Mathlib.Algebra.Order.Hom.Units` and `Mathlib.NumberTheory.LocalField.Basic`.
Stating M248.002 needs only `localCompleteDVF` and `Valuation.HasExtension`.
`FiniteIntegralClosure` serves the chosen-extension part of the original file.
No external NYLL repository module is imported.

Existing related declarations are different statements. The published
`Langlands.NYLL.LocalFieldTheory.hasExtension_comap_ringEquivsStatement` and
`hasExtension_of_isEquivStatement` state generic transport of
`HasExtension` along ring equivalences and equivalent valuations. They do not
mention the canonical packages. The published
`Langlands.LocalClassField.NYLL.SuppliedRelativeValuationExtensionStatement`
states the canonical `HasExtension` relation itself for supplied `p`-adic field
data. That is the kind of premise this statement assumes, not its conclusion.
This statement neither replaces nor proves it.

## Development checks

The module compiles in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
Declaration inspection reports a definition with level parameters `u, v`
whose type is `Prop`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

A separate private check module, which is not part of this submission, did
three things:

- It printed the complete unapplied definition with explicit universes and
  instances. This displayed exactly the telescope above. The premise and
  conclusion both use the supplied `Algebra K L` instance. The conclusion is
  `Valuation.HasExtension.{u,v,u,v}` between the `CompleteDVF.valuation`
  projections of `localCompleteDVF.{u} K` and `localCompleteDVF.{v} L`.
- It checked by `Iff.rfl` that the definition unfolds to the source signature
  written with the source's dot notation.
- It checked that the source's proof, with only the binders introduced,
  elaborates against this definition.

These checks establish compilation and the correspondence stated here.
Semantic review and publication are separate steps.

## Attribution and modifications

The complete 206-line original was read. Its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The workspace, project notes and Library used for this adaptation contain no
source-specific errata directory.

The original copyright and author header is retained verbatim. The inherited,
unmodified [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) apply. Their SHA256 values
are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE has no entry for the selected source file. The
third-party source table `Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md` in
the supplement does not list it either. The supplement's
`.github/verification/publication.json` records the SHA256 given above.

On 30 October 2026, Worker 785 extracted the statement and made the
namespace, naming, closed-quantification, notation and import changes listed
above. Worker 785 also wrote this explanation. Worker 106 supplied routing
only. No unpublished implementation or draft from another worker was reused.
