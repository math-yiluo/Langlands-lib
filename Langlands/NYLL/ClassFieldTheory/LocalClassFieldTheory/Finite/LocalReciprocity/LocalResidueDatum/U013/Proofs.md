# Naturality of the base-residue comparison: proof (M249.013)

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue_algebraMap`.
Its type is the already published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue_algebraMapStatement`
of the module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U013.Statements`:

```lean
theorem localBaseResidueEquivDecompositionResidue_algebraMap :
    localBaseResidueEquivDecompositionResidue_algebraMapStatement
```

This is the proof phase of M249.013 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m249).
No other declaration is added. The theorem has no universe parameter: as in
the source, the field `K` lives in `Type`.

## Target and binders

By its definition in the statement module, the target is

```lean
∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (localCompleteDVF K).valuationSubring),
    algebraMap
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (localBaseResidueEquivDecompositionResidue K
          (IsLocalRing.residue (localCompleteDVF K).valuationSubring x)) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨algebraMap K (SeparableClosure K) (x : K),
          (localSeparableValuationSubring_pullback K (x : K)).2
            x.property⟩ : localSeparableValuationSubring K)
```

Write `𝒪` for the valuation ring `(localCompleteDVF K).valuationSubring` of
the canonical complete discrete valuation of the nonarchimedean local field
`K`, `k` for its residue field, `B` for the valuation ring
`localSeparableValuationSubring K` of `SeparableClosure K` (M249.006), `Z`
for the decomposition group of `B` over `K`, `κ = decompositionResidueField K B`
for the quotient of the fixed subring `B^Z` by the contraction of the
maximal ideal of `B` (M243.003), and `λ = selectedResidueField B`, the
residue field of `B` (M243.004). The statement says that for every
`x ∈ 𝒪`, reducing `x` modulo the maximal ideal of `𝒪`, applying the
comparison `φ = localBaseResidueEquivDecompositionResidue K : k ≃+* κ`
(M249.012) and then the algebra map `κ → λ` (the instance
`selectedResidueField.instAlgebra`, M243.021) gives the residue in `λ` of the
image `algebraMap K (SeparableClosure K) x`, which lies in `B` by the
backward direction of the published M249.007 theorem
`localSeparableValuationSubring_pullback`.

The binders are the source section variables `K` and its four instance
binders (source lines 45–46), followed by the theorem's own binder `x`. No
hypothesis is added. The paired Markdown of the statement module describes
all published declarations in the target.

The sole direct import is the published `U013.Statements` module, which
supplies the target and, through its imports, every definition named in it
(including `LocalResidueDatum.U011.Definitions`, which defines `φ` and
imports the M249.007 and M249.010 proof modules).

## Implemented proof

```lean
intro K _ _ _ _ x
rfl
```

1. `intro K _ _ _ _ x` introduces the six binders. The goal is the equation
   above for these `K` and `x`.
2. `rfl` closes it: both sides are definitionally equal elements of `λ`.

The definitional equality holds because every map on the left-hand side is
defined on representatives, and each representative is carried to the same
element of `SeparableClosure K`:

- `φ` is, by its definition in `U011.Definitions`, the residue-field map
  `IsLocalRing.ResidueField.mapEquiv` of the ring isomorphism
  `Langlands.NYLL.PortInternal.M249.d011 K` from `𝒪` onto the valuation ring
  of the decomposition field (M249.011), followed by
  `decompositionFieldResidueEquiv` (M243.018). The residue-field map sends
  the residue class of `x` to the residue class of `d011 K x`, whose
  underlying element of `SeparableClosure K` is
  `algebraMap K (SeparableClosure K) x` by the construction of `d011` (its
  body records this as a `rfl` step).
- `decompositionFieldResidueEquiv` is the residue-field map of
  `decompositionFieldValuationSubringEquivFixedSubring`, which keeps the
  underlying element of `SeparableClosure K`, followed by the quotient
  identification `Ideal.quotientEquivAlgOfEq`, which sends a class to the
  class of the same representative. So `φ` sends the residue class of `x` to
  the class in `κ` of the element of `B^Z` with underlying element
  `algebraMap K (SeparableClosure K) x`.
- The algebra map `κ → λ` is `Ideal.Quotient.algebraQuotientOfLEComap`,
  which sends the class of `z ∈ B^Z` to the residue class of `z` in `B`.

The resulting residue class in `λ` is the right-hand side; the membership
proofs inside the subtype elements may differ but are equal by proof
irrelevance. Lean's elaborator and kernel check this unfolding; no lemma is
cited.

The development check reports that the theorem has no level parameters and
uses only `propext`, `Classical.choice` and `Quot.sound`, all already used
by the imported definitions and Mathlib; the proof adds no further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`,
lines 235–250](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean#L235-L250):
the docstring at 235–238, the signature at 239–249 and the proof

```lean
  rfl
```

(after `:= by` on line 249) at line 250. The passage lies in the
`LocalClassFieldTheory` namespace (line 31) and its `noncomputable section`
(line 39), with the opens of lines 33–43 and the section variables `K` and
its instance binders at lines 45–46. The source section also declares the
local instances `localSeparableClosureAlgebra` and
`localSeparableClosureScalarTower` (from line 48); neither occurs in the
target, as the paired Markdown of the statement module records, and the
proof here does not use them. The complete original file is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`;
it was read and its SHA-256 hash verified as
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`, the hash
recorded in the partition, which records no patch10 change to this module.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| `LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue_algebraMap` (theorem) | `localBaseResidueEquivDecompositionResidue_algebraMap` (theorem), proving the published target |
| Same theorem's statement | Existing `localBaseResidueEquivDecompositionResidue_algebraMapStatement` |
| `localBaseResidueEquivDecompositionResidue` (M249.012), private `localBaseValuationSubringEquivDecompositionField` (M249.011) | Existing published `localBaseResidueEquivDecompositionResidue` and `Langlands.NYLL.PortInternal.M249.d011`, unfolded by `rfl` |
| `localSeparableValuationSubring_pullback` (M249.007), in the statement | Existing published theorem |

Only the first row introduces a declaration here. Modifications by
Worker 127 on 15 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the sole `U013.Statements` import;
- give the theorem the published closed statement as its type and introduce
  its binders with `intro K _ _ _ _ x`, then close the goal with the source
  proof `rfl`;
- omit the source `noncomputable section`, the source opens and local
  instances, which this proof does not need, and all other source
  declarations.

The theorem name and docstring are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the Library, staging and shared drafts found no earlier proof
port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with no diagnostics. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 127 adapted this proof directly from
the pinned original and wrote this companion; Worker 85, who routed the
task, had replayed the same source proof privately, and their task notes
were consulted. No other code or reused draft was supplied. The published
`U013.Statements` module, all other imported Library modules and their
paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) remain in the Library
and are byte-identical to the retained originals. Their SHA-256 hashes are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This module proves only M249.013. It does not publish M249.014 or any other
M249 declaration.
