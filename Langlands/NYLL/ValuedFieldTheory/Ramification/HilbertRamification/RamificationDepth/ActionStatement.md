# NYLL M323.001: additive valuation preserved by the unique-extension action

This module extracts M323.001, lines 33–44; surrounding section parameters at lines 20–29 from Naganori Yamaguchi's *ClassFieldTheory*,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationDepth.lean` (whole-file SHA-256 `443b4046f6fbacd7ad8760bfd6116ec5a4f182727e01d7fd931ce6e11eef0d1c`).
The original copyright and author header is preserved. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
its Apache-2.0 attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found in the Library errata filenames.

## Exact proposition and source correspondence

All definitions below lie in `Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`. Each original theorem name is
prefixed with `Langlands.NYLL` and gains the suffix `Statement`. Their full
proposition bodies, including every source parameter and hypothesis, are:

```lean
def addVal_valuationSubringAutOfUniqueExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) (a : target.valuationSubring),
    _root_.IsDiscreteValuationRing.addVal target.valuationSubring
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a) =
      _root_.IsDiscreteValuationRing.addVal target.valuationSubring a
```

For the source four independent universes, supplied valuation extension and uniqueness predicate, the actual valuation-ring action of every K-automorphism preserves the normalized additive valuation. No completeness, finite-dimensionality, Galois or separable-residue assumption is added. The action is exactly the published M304.014 ring equivalence, so the source proof reduces to M311.002.

## Modifications and dependency boundary

Worker 296 extracted the displayed source signatures into closed `def`s returning
`Prop`: section parameters and theorem binders now occur under `∀` inside the
proposition. The source binder kinds and parameter order are retained, as are all
independent universe levels and hypotheses. The proofs, theorem attributes and
unused surrounding declarations are omitted. The namespace gains the prefix
`Langlands.NYLL`. Source names for the two DVF namespaces are expanded to the
published qualified names; Mathlib constants keep their original meaning.

The source's whole-module imports are replaced by exactly these focused imports:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`.

These are proposition targets; this module supplies no proof of them. In
particular, it adds no premise assuming its conclusion and no global instance.
The targets refer directly to the published data with the corresponding Lean
names. Compilation and proposition inspection are development evidence only;
independent semantic acceptance and publication remain required.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with hashes `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No feasibility proof patch or unpublished draft is reused here. The target
environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
