# Antitonicity of the actual local upper ramification filtration

This module proves the published closed proposition
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_antitoneStatement`
from module
`Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.AntitoneStatement`.
The theorem is
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_antitone`.
Worker 314 reuses Worker 296's implementation from the parent task's shared draft
revision 3, with an added preparation notice and expanded documentation.

## Exact target

In namespace `Langlands.NYLL.RamificationTheory.LocalField`, with
`Langlands.NYLL.LocalFieldTheory` open, the imported proposition is:

```lean
def localUpperRamificationGroup_antitoneStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Antitone (localUpperRamificationGroup K L)
```

The theorem's declared type is exactly this proposition, without added premises.
It retains the source's Type 0 fields and all its hypotheses. For every pair of
real indices `s ≤ t`, it proves the actual subgroup inclusion
`localUpperRamificationGroup K L t ≤ localUpperRamificationGroup K L s`.
Neither a valuation nor a topology on `L` is an extra parameter.

## Implemented proof and published inputs

The proof introduces the fields, instances and real indices. It installs only
the local witness

```lean
let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
    (chosenLocalExtensionCompleteDVF K L).valuation :=
  Classical.choose (chosenLocalExtension_properties K L)
```

This is the same witness used inside the published definition of
`localUpperRamificationGroup`. The uniqueness proof is the published
`Langlands.NYLL.LocalFieldTheory.chosenLocalExtension_uniqueValuationExtension.{0} K L`;
the explicit universe is the comparison value-group universe required by those
definitions.

Unfolding the local upper group exposes the actual unique-extension upper group,
definitionally the lower group evaluated at the inverse Herbrand function.
The proof applies these published theorems, whose namespace is
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`:

- `lowerRamificationGroup_antitone`, from
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupProof`.
- `inverseHerbrandFunctionOfUniqueExtension_strictMono`, from
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof`.

The second theorem's `.monotone` maps `s ≤ t` to ordered lower indices; the first
reverses that order to give the required inclusion. The lower-group theorem is
available through the published import closure of the two direct imports:
`AntitoneStatement` and `HilbertRamification.HerbrandFunction.LawsProof`, with
their full module prefixes as above. The local extension and uniqueness proofs
come through `AntitoneStatement`'s published `Core.Definitions` import.
There is no new global `Valuation.HasExtension` instance or M326 quotient-theorem
dependency.

## Original source and modifications

The source is Naganori Yamaguchi's *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`, M327.010,
lines 736–748. Its whole-file SHA-256 is
`d0e79ce27df3b1f7481d2e6c89473f600acaf21f0cf4b678e29ba97a90792ecb`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the Library errata filenames.

Relative to M327.010, the namespace gains `Langlands.NYLL`; the whole-module
imports become the two focused published imports; and the source telescope is
introduced from the already published closed proposition. The proof retains the
source's antitone-lower-group/monotone-inverse-Herbrand route. It replaces the
source's ambient global extension instance by the local witness displayed above,
and replaces `chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension`
by the published `chosenLocalExtension_uniqueValuationExtension.{0}`. It omits
the surrounding declarations and preserves the theorem name after prefixing.
The target pair and all its dependencies are imported unchanged.

The original copyright and author header and Apache-2.0 attribution are retained
in the Lean file, with modification notices. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The target environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
