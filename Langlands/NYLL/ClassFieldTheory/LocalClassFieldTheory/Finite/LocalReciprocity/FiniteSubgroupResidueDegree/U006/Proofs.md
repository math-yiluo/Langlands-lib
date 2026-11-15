# The local residue action restricted to a closed subgroup: proof (M250.006)

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedResidueAction_apply`.
Its type is the already published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedResidueAction_applyStatement`
of the module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U006.Statements`
([target](Statements.md)):

```lean
theorem localAbstractFixedResidueAction_apply :
    localAbstractFixedResidueAction_applyStatement
```

This is the proof phase of M250.006 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m250).
No other declaration is added. The theorem has no universe parameter: as in
the source, the field `K` lives in `Type`.

## Target and binders

By its definition in the statement module, the target is

```lean
∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    (sigma : H.toSubgroup)
    (x : selectedResidueField (localSeparableValuationSubring K)),
    localSeparableResidueAlgAction K sigma.1 x =
      residueAlgActionOfEqTop
        (abstractFixedField K (SeparableClosure K) H)
        (localSeparableValuationSubring K)
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma) x
```

For a nonarchimedean local field `K`, write `B` for the valuation ring
`localSeparableValuationSubring K` of `SeparableClosure K` (M249.006), `Ω`
for its residue field `selectedResidueField B`, which is Mathlib's
`IsLocalRing.ResidueField B` (M243.004), `H` for a closed subgroup of
`Gal(SeparableClosure K/K)` and `E = abstractFixedField K (SeparableClosure K) H`
(M099.001) for its fixed field. The statement says that for `sigma ∈ H` and
`x ∈ Ω`, the local residue action of `sigma` (M249.020) and the residue
action over `E` (M244.003) of the corresponding automorphism
`abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma` of
`SeparableClosure K` over `E` (M099.007) take the same value at `x`.

The binders are the source section variables `K` and its four instance
binders (source lines 33–34), followed by the theorem's own binders `H`,
`sigma` and `x` (lines 103–105). No hypothesis is added. The paired
[Markdown of the statement module](Statements.md) describes the published
declarations in the target, including the `IsGalois` instance found by
instance search.

## Dependencies

The only direct import is the published `U006.Statements` module, which
supplies the target. Every other name in the proof is already in scope
through it:

| Name used in the proof | Role | Where it comes from |
| --- | --- | --- |
| `localSeparableValuationSubring` (M249.006) | the valuation ring `B` | [`LocalResidueDatum.U006.Definitions`](../../LocalResidueDatum/U006/Definitions.md), imported through the target's imports |
| `toDecompositionGroupOfEqTop` (M244.001) | views an automorphism as an element of the decomposition group when that group is everything | [`ResidueActionIndex.U001.Definitions`](../../ResidueActionIndex/U001/Definitions.md), imported through `ResidueActionIndex.U003.Definitions` |
| `localSeparableDecompositionGroup_eq_top` (M249.010) | proof that the decomposition group of `B` over `K` is everything, applied as `... K` | published proof in [`LocalResidueDatum.U010.Proofs`](../../LocalResidueDatum/U010/Proofs.md), imported through the M249.020 and M250.005 modules |
| `localAbstractFixedDecompositionGroup_eq_top` (M250.005) | the same over `E`, applied as `... K H` | published proof in [`U005.Proofs`](../U005/Proofs.md), a direct import of the target |
| `abstractFixedField`, `abstractSubgroupEquivGaloisGroup` (M099.001, M099.007) | `E` and the identification of `H` with `Gal(SeparableClosure K/E)` | [`FiniteAbstractFixedField.Initial.Definitions`](../../FiniteAbstractFixedField/Initial/Definitions.md), imported through `U005.Proofs` |
| `IsLocalRing.residue`, `IsLocalRing.residue_surjective`, `SeparableClosure` | the residue map `B → Ω`, its surjectivity, and the separable closure | Mathlib |

The `change` step also relies on the definitions behind the two sides,
which it unfolds without naming them: `localSeparableResidueAlgAction K`
([M249.020](../../LocalResidueDatum/U020/Definitions.md)) has underlying
monoid homomorphism
`residueAlgActionOfEqTop K B (localSeparableDecompositionGroup_eq_top K)`;
`residueAlgActionOfEqTop` ([M244.003](../../ResidueActionIndex/U003/Definitions.md))
is `decompositionGroupResidueAction` composed with
`toDecompositionGroupOfEqTop`; and `decompositionGroupResidueAction`
([M243.024](../../../../../../ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence/ResidueAction.md))
is Mathlib's `Ideal.Quotient.stabilizerHom` for the maximal ideal of `B`,
composed with the identification of the decomposition group with the
stabilizer of that ideal. Mathlib's `Ideal.Quotient.stabilizerHom_apply`
holds by `rfl`: the image of `g` sends the class of `b` to the class of
`g • b`. Here `g • b` is Mathlib's action
`ValuationSubring.decompositionSubgroupMulSemiringAction` of the
decomposition subgroup on `B`, by applying the underlying automorphism.

## Implemented proof

```lean
intro K _ _ _ _ H sigma x
let A := localSeparableValuationSubring K
obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
change IsLocalRing.residue A
    ((toDecompositionGroupOfEqTop K A
      (localSeparableDecompositionGroup_eq_top K) sigma.1) • a) =
  IsLocalRing.residue A
    ((toDecompositionGroupOfEqTop
      (abstractFixedField K (SeparableClosure K) H) A
      (localAbstractFixedDecompositionGroup_eq_top K H)
      (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma)) • a)
congr 1
```

1. `intro K _ _ _ _ H sigma x` introduces the eight binders of the closed
   target (Lean unfolds the `def` for `intro`); `A` names `B`.
2. `obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x` writes `x` as the
   residue class `IsLocalRing.residue A a` of some `a : A`.
3. `change` restates the goal, up to definitional unfolding, as an equation
   between the residue classes of `g₁ • a` and `g₂ • a`, where
   `g₁ = toDecompositionGroupOfEqTop K A (localSeparableDecompositionGroup_eq_top K) sigma.1`
   is `sigma` as an element of the decomposition group of `B` over `K`, and
   `g₂` is `abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma`
   as an element of the decomposition group of `B` over `E`. The left side
   unfolds through `localSeparableResidueAlgAction`, `residueAlgActionOfEqTop`,
   `decompositionGroupResidueAction` and `Ideal.Quotient.stabilizerHom` as
   described above, and the right side through the last three of them.
   This step is needed: without it, `congr 1` leaves unsolved goals that
   compare the two different automorphism groups of `Ω` (over
   `decompositionResidueField K B` and over `decompositionResidueField E B`)
   and their elements heterogeneously.
4. `congr 1` reduces the goal to `g₁ • a = g₂ • a` in `A` and closes it by
   reflexivity. Both elements of `A` have underlying value `sigma.1 a` by
   definition: `toDecompositionGroupOfEqTop` keeps the underlying
   automorphism, and `abstractSubgroupEquivGaloisGroup`, built from
   Mathlib's `MulEquiv.subgroupCongr` and
   `IntermediateField.fixingSubgroupEquiv`, does not change the underlying
   map of `SeparableClosure K`.

A private probe (development evidence only) confirmed steps 3 and 4: after
the `change`, `apply congrArg (IsLocalRing.residue A)` followed by `rfl`
also closes the goal; both coercions of `g₁ • a` and `g₂ • a` to
`SeparableClosure K` equal `sigma.1 a` by `rfl`; and `congr 1` without the
preceding `change` fails as described in step 3.

The development check reports that the theorem has no level parameters and
uses only `propext`, `Classical.choice` and `Quot.sound`, all already used
by the imported definitions and Mathlib; the proof adds no further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`,
lines 99–122](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean#L99-L122):
the docstring at 99–101, the signature at 102–111 and the proof at 112–122
(line 123 is blank; the target's Markdown and the task cite the proof as
lines 112–123),

```lean
  let A := localSeparableValuationSubring K
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop K A
        (localSeparableDecompositionGroup_eq_top K) sigma.1) • a) =
    IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop
        (abstractFixedField K (SeparableClosure K) H) A
        (localAbstractFixedDecompositionGroup_eq_top K H)
        (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H sigma)) • a)
  congr 1
```

The passage lies in the `LocalClassFieldTheory` namespace (line 20) and its
`noncomputable section` (line 27), with the opens of lines 21–31 and the
section variables `K` and its instance binders at lines 33–34. The complete
original file is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`;
it was read and its SHA-256 hash verified as
`84865498b7b4788c2ebeecb92aeaca7a1bb9a62e2005cb1554386e2a52bf674a`, the hash
recorded in the partition, which records no patch10 change to this module.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| `LocalClassFieldTheory.localAbstractFixedResidueAction_apply` (theorem) | `localAbstractFixedResidueAction_apply` (theorem), proving the published target |
| Same theorem's statement | Existing `localAbstractFixedResidueAction_applyStatement` |
| `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (M249.010) | Existing published theorem of `LocalResidueDatum.U010.Proofs` |
| `LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_top` (M250.005) | Existing published theorem of `U005.Proofs` |
| `toDecompositionGroupOfEqTop`, `abstractFixedField`, `abstractSubgroupEquivGaloisGroup`, `localSeparableValuationSubring` | Existing published definitions (M244.001, M099.001, M099.007, M249.006) |

Only the first row introduces a declaration here. Modifications by
Worker 127 on 15 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the `U006.Statements` import;
- give the theorem the published closed statement as its type and introduce
  its binders with `intro K _ _ _ _ H sigma x`;
- keep the source proof, lines 112–122, unchanged (a line-by-line
  comparison of those lines with the tactic lines after the `intro` found
  no difference, indentation included); the names
  `localSeparableDecompositionGroup_eq_top` and
  `localAbstractFixedDecompositionGroup_eq_top` now denote the published
  closed M249.010 and M250.005 theorems, applied to `K` and to `K H` as in
  the source;
- omit all source `open` lines (lines 21–31): every name the proof writes
  lies in `Langlands.NYLL.LocalClassFieldTheory` or is a Mathlib name
  written in full (`SeparableClosure`, `IsLocalRing.residue`,
  `IsLocalRing.residue_surjective`), and the development check compiled
  the module with no diagnostics without any `open`. Also omit the source `noncomputable section` and all
  other source declarations.

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
`U006.Statements` module, all other imported Library modules and their
paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) remain in the Library
and are byte-identical to the retained originals. Their SHA-256 hashes are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file; Mathlib lemmas are only used by
name.

This module proves only M250.006. It does not publish M250.007 or any other
M250 declaration.
