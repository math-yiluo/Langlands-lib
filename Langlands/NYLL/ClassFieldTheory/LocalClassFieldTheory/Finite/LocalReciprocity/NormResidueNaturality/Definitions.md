# Continuous restriction between finite Galois intermediate fields

`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldRestrictContinuous` is
the restriction `Gal(F/K) → Gal(E/K)` for finite Galois intermediate fields
`E ≤ F` of `SeparableClosure K / K`, bundled as a continuous monoid
homomorphism. In Lean:

```lean
variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def intermediateFieldRestrictContinuous
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F] :
    Gal(F / K) →ₜ* Gal(E / K) :=
  { intermediateFieldRestrictNormalHom E F hEF with
    continuous_toFun := continuous_of_discreteTopology }
```

## Telescope

`K` lies in `Type 0`, as in the source, and the declaration has no universe
parameters. The section declares three local-field instances on `K`, but
neither the type nor the body uses them. Lean therefore does not make them
parameters of the definition. A `#check` of the compiled declaration in the
approved environment prints exactly:

```lean
intermediateFieldRestrictContinuous : (K : Type) → [inst : Field K] →
  (E F : IntermediateField K (SeparableClosure K)) → E ≤ F →
  [FiniteDimensional K ↥E] → [FiniteDimensional K ↥F] →
  [IsGalois K ↥E] → [IsGalois K ↥F] → Gal(↥F/K) →ₜ* Gal(↥E/K)
```

So the explicit arguments are `K`, `E`, `F` and `hEF`. The other arguments are
`[Field K]` and the two finite-dimensionality and two Galois instances.
Callers need no `ValuativeRel`, topology or local-field instance on `K`. The
Lean file keeps the source's `variable` line, declaration and body unchanged,
so Lean's variable-inclusion rule gives the source declaration the same
telescope. The source targeted Lean 4.35.0-rc2.

## Mathematical content

- The underlying monoid homomorphism is the published M259.001 restriction
  `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom E F hEF`,
  with `Omega := SeparableClosure K`. Its normality hypothesis `[Normal K E]` is
  supplied by `[IsGalois K E]`. It sends `sigma` to the unique automorphism of
  `E` that commutes with `sigma` through the inclusion `E ≤ F`.
- `Gal(F / K)` and `Gal(E / K)` carry Mathlib's Krull topology
  (`Mathlib/FieldTheory/KrullTopology.lean`). For a finite-dimensional
  extension this topology is discrete, by the instance
  `krullTopology_discreteTopology_of_finiteDimensional` (lines 247–248).
- Continuity is therefore `continuous_of_discreteTopology`: every map out of a
  discrete space is continuous.
- `→ₜ*` is Mathlib's `ContinuousMonoidHom`
  (`Mathlib/Topology/Algebra/ContinuousMonoidHom.lean`, line 57), a monoid
  homomorphism bundled with a proof of continuity.

`SeparableClosure K` is Mathlib's abbreviation
`separableClosure K (AlgebraicClosure K)` (`Mathlib/FieldTheory/IsSepClosed.lean`,
line 349). The construction assumes nothing beyond the four
finite-dimensionality and Galois instances on `E` and `F` listed above.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean`.
The relevant lines are:

- the section variables at lines 26–27;
- the docstring at lines 29–31;
- the definition at lines 32–38.

The file's SHA-256 is
`6ce6bed397d0b568e82edfeed9a68b46ceec73202af7314ac344ac3283dcf7c3`. The
source opens `LocalFieldTheory` and `RamificationTheory`, and refers to the
restriction by its short name.

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.intermediateFieldRestrictContinuous` (M261.001) | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldRestrictContinuous` |
| `RamificationTheory.intermediateFieldRestrictNormalHom` (M259.001) | Published `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom` (imported, not redefined) |

Only the first row introduces a declaration in this module. The target name is
the one given for row M261.001 in the published partition
[`notes/reuse/nyll-public-port/m259-m262.md`](../../../../../../../notes/reuse/nyll-public-port/m259-m262.md),
following
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../notes/reuse/nyll-public-port-plan.md).
No NYLL erratum for this module was found in the current Library's `notes/`.

## Imports and modification record

The source imports the NYLL modules `NormResidue` and
`IntermediateFieldNormResidueNaturality`. This definition needs neither of
their local-reciprocity contents, so the adapted module imports only:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions`
  (published M259.001), for the restriction homomorphism;
- `Mathlib.FieldTheory.IsSepClosed`, for `SeparableClosure`;
- `Mathlib.FieldTheory.KrullTopology`, for the Krull topology and its
  discreteness in finite degree;
- `Mathlib.NumberTheory.LocalField.Basic`, for the class
  `IsNonarchimedeanLocalField` named in the retained `variable` line;
- `Mathlib.Topology.Algebra.ContinuousMonoidHom`, for `→ₜ*`.

`IsNonarchimedeanLocalField` is Mathlib's class
(`Mathlib/NumberTheory/LocalField/Basic.lean`, lines 45–49). It is not an NYLL
definition. Every transitive import is either the published M259.001 module or
part of the approved Mathlib environment. No external NYLL module is imported.

The adaptation makes these changes:

- it prefixes the namespace with `Langlands.NYLL`;
- it splits this definition out as its own `Definitions` module, omitting the
  M261.002 and M261.003 theorems that follow it;
- it replaces the source's `open LocalFieldTheory` and `open RamificationTheory`
  with `open Langlands.NYLL.RamificationTheory`. Nothing from
  `LocalFieldTheory` is used;
- it replaces the imports as listed above.

The source's `noncomputable section`, section `variable` line, docstring,
argument order, binder kinds, return type and body are unchanged. The Lean
header records these changes with Worker 30's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
with no universe parameters and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not independent
acceptance.

## License

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 30
adapted this unit directly from the pinned original; no other project worker
supplied code. The imported M259.001 module and its Markdown are unchanged.
