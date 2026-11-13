# Chosen uniformizer as a field unit, and its inverse (M133.007, M133.009)

For a nonarchimedean local field `K`, this module defines two units of `K`:

- `Langlands.NYLL.LocalFieldTheory.integerRingUniformizerFieldUnit K : Kˣ`,
  the published chosen uniformizer `chosenIntegerRingUniformizer K : 𝒪[K]`
  viewed as a nonzero element of `K`;
- `Langlands.NYLL.LocalFieldTheory.inverseIntegerRingUniformizerFieldUnit K : Kˣ`,
  the inverse of that unit.

In Lean:

```lean
def integerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Units.mk0 (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) (by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible K).ne_zero (Subtype.ext h))

def inverseIntegerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  (integerRingUniformizerFieldUnit K)⁻¹
```

They are extracted from Naganori Yamaguchi's NYLL ClassFieldTheory,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The original file has
SHA-256 `8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also
registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

## Source correspondence

Every original name below is in `LocalFieldTheory`; every adapted name is
in `Langlands.NYLL.LocalFieldTheory`.

| Unit | Original name | Source lines (docstring, declaration) | Adapted name |
| --- | --- | --- | --- |
| M133.007 | `integerRingUniformizerFieldUnit` | 69–73, 74–79 | `integerRingUniformizerFieldUnit` |
| M133.009 | `inverseIntegerRingUniformizerFieldUnit` | 91–95, 96–99 | `inverseIntegerRingUniformizerFieldUnit` |

The source file opens `namespace LocalFieldTheory` (line 12), a
`noncomputable section` (line 14), `universe u` (line 16) and
`open scoped ValuativeRel` (line 18). It declares no `variable`, so the
binders shown are the whole telescope. Both definitions take the universe
`u`, an explicit `(K : Type u)`, then the instance arguments `[Field K]`,
`[ValuativeRel K]`, `[TopologicalSpace K]` and
`[IsNonarchimedeanLocalField K]`, in that order. No argument is added,
removed, reordered or rebound. `IsNonarchimedeanLocalField` is Mathlib's
class (`Mathlib/NumberTheory/LocalField/Basic.lean`); `𝒪[K]` is Mathlib's
scoped notation for the valuation integers of `K`.

The bodies are the source bodies, character for character:

- M133.007 applies `Units.mk0` to the image of `chosenIntegerRingUniformizer K`
  in `K` (the coercion of the subring `𝒪[K]`). The nonvanishing proof is the
  source tactic block. If the image were `0`, then `Subtype.ext` makes the
  chosen element `0` in `𝒪[K]`, which contradicts `Irreducible.ne_zero` applied
  to the irreducibility of the chosen uniformizer.
- M133.009 is the group inverse of M133.007 in `Kˣ`.

The source docstrings are retained. The phrase "With the normalized additive
valuation used by `valuationMap`, this is the element expected to have value
`1`" in the M133.009 docstring is the source's remark. NYLL's normalized
valuation gives a prime element the value `-1`, so its inverse has value `1`
(see the Library note `notes/reuse/nyll-finite-local-reciprocity-audit.md`,
section 2.3). This module neither states nor proves that normalization. The
statement targets M133.015/.016 in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements`
express it for an arbitrary irreducible element.

The proof term inside M133.007 uses the published theorem
`Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer_irreducible`
(source unit M133.005). Its type is the published Prop-valued target
`chosenIntegerRingUniformizer_irreducibleStatement K`, which unfolds to
`Irreducible (chosenIntegerRingUniformizer K)`. Lean's generalized field
notation unfolds this definition, so the source expression
`(chosenIntegerRingUniformizer_irreducible K).ne_zero` elaborates unchanged
to `Irreducible.ne_zero`. Because the proof is a proposition, the value of the
unit depends only on `chosenIntegerRingUniformizer K`.

The port-plan partition
[`notes/reuse/nyll-public-port/m121-m144.md`](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md)
(rows M133.007 and M133.009) reserves exactly these adapted names.

## Reuse and modifications

The only import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs`,
the published module that proves M133.005. Through its imports it supplies
the published `chosenIntegerRingUniformizer` (M133.004, module
`...IdealQuotients.Definitions`), the target
`chosenIntegerRingUniformizer_irreducibleStatement` (module
`...IdealQuotients.Statements`), Mathlib's local-field class, the scoped
notation and `Units.mk0`. The source's two imports (`PrincipalUnitQuotients`
and a cardinal module) are not needed for these definitions and are omitted.
No same-named declaration exists in the current Library or Mathlib.

Worker 85 extracted exactly these two source definitions on 13 November 2026.
The Lean header records the change. The changes are:

- the namespace is prefixed with `Langlands.NYLL`;
- the imports are replaced as described above.

The definition bodies, result types, universes, parameter telescopes,
docstrings and the `noncomputable section` are unchanged. The source's
`@[simp]` lemmas M133.008 `integerRingUniformizerFieldUnit_coe` and
M133.010 `inverseIntegerRingUniformizerFieldUnit_coe` (both proved by `rfl`)
are not part of this module. Every other declaration of the source file is
also omitted. No theorem, private helper, instance, notation or alias is
introduced.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of
`integerRingUniformizerFieldUnit` reports a definition with level parameter `u`
and only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
This development check is not independent acceptance.

## Use downstream

The two units are the base data of the source's prime-element decompositions.
In the port they appear in the statement targets
`v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement`
(M162.017) and
`v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement`
(M162.018) in `Langlands.NYLL.LocalClassFieldTheory`.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 85 adapted these units directly from the
pinned original; no other project worker supplied code.
