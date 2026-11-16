# Finite abstract-field degree and fixed-field finrank

Worker 203 adapts source unit M330.006 and proves the existing proposition
`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractField_degree_eq_abstractFixedField_finrankStatement`
under the theorem name
`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractField_degree_eq_abstractFixedField_finrank`.
The proof imports the published `DegreeStatement` module by Lean name.
Worker 305 supplied the direct Mathlib feasibility route recorded in the task;
this pair implements that route as the named theorem.

The parameters are exactly `(K : Type) [Field K]`, explicit
`H : Langlands.NYLL.ClassFormation.FiniteAbstractField (Gal(SeparableClosure K/K))`,
and explicit `hnormal` asserting

```lean
(Langlands.NYLL.CyclicCohomology.extensionSubgroup
  (Langlands.NYLL.ClassFormation.baseField (Gal(SeparableClosure K/K)))
  H.field (Langlands.NYLL.ClassFormation.le_baseField H.field)).Normal
```

The conclusion is the published target applied to `K H hnormal`, whose body is

```lean
(H.toFiniteAbstractExtension.degree : ℕ) =
  Module.finrank K
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedField
      K (SeparableClosure K) H.field)
```

The abstract degree is the positive natural degree of the existing finite
abstract extension, coerced to a natural number. The concrete field is the
actual intermediate fixed field
`IntermediateField.fixedField H.field.toSubgroup` in `SeparableClosure K`.
Its field and `K`-module structures are the published canonical ones.

## Implemented proof

The proof unfolds only the target with `change` and follows four equalities.

1. `DegreeData.FiniteAbstractExtension.degree` has natural value
   `Nat.card` of its actual relative coset space. Applying
   `(Subgroup.index_eq_card _).symm` identifies this with the index of
   `extensionSubgroup (baseField _) H.field (le_baseField H.field)` in the
   base subgroup. The quotient and subgroup presentations agree by definition.
2. `baseField` is the top closed subgroup. Rewriting the opposite equality by
   `← Subgroup.relIndex_top_right` reduces this relative index to
   `H.field.toSubgroup.index`; the remaining equality is definitional.
3. `InfiniteGalois.fixingSubgroup_fixedField H.field` identifies the fixing
   subgroup of the concrete fixed field with the given closed subgroup.
   Applying `congrArg Subgroup.index` to its symmetric equality transfers the
   index.
4. The symmetric
   `IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) _`
   identifies that fixing-subgroup index with the fixed field's finrank.

The last two steps use that the ambient extension `SeparableClosure K / K`
is Galois. They require no separate `IsGalois K` instance for the fixed field
and no supplied `FiniteDimensional K` instance for it. In particular, the
normality hypothesis is retained as an explicit argument of the theorem and
its target, while the equality proof does not use it.

The Mathlib replacements are at the approved pin
`5ed2965256430c3649e86755f9576b54eca72435`:

| Declaration | Source |
| --- | --- |
| `Subgroup.index_eq_card` | `Mathlib/GroupTheory/Index.lean:348` |
| `Subgroup.relIndex_top_right` | `Mathlib/GroupTheory/Index.lean:268` |
| `InfiniteGalois.fixingSubgroup_fixedField` | `Mathlib/FieldTheory/Galois/Infinite.lean:146` |
| `IntermediateField.finrank_eq_fixingSubgroup_index` | `Mathlib/FieldTheory/Galois/Basic.lean:678` |

## Source correspondence and modifications

The original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean`.
Its SHA-256 is
`095bea2e9d86b74ce22127ea88332ca81fd0433ef86e5e9442bb37363930ca53`.
The original theorem is
`LocalClassFieldTheory.finiteAbstractField_degree_eq_abstractFixedField_finrank`,
unit M330.006 in the public partition
`notes/reuse/nyll-public-port-plan.md`. The docstring is at lines 190–191,
the telescope and conclusion at 192–208, and the proof at 209–230.
The readable source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The existing source registrations are
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No matching NYLL source errata note was found in the checked Library and
project errata directories.

Every modification to this extracted proof is as follows:

- Prefix the namespace with `Langlands.NYLL`; preserve the original theorem
  name, docstring, universe-zero `K : Type`, binder order, instance binder
  `[Field K]`, and explicit `H` and `hnormal` with the full subgroup expression.
- Express the conclusion as the published target applied to all its
  parameters. That target already substitutes the source's local `E` and
  reduces the two unused local instance lets in the original conclusion.
  The published target and its dependencies are unchanged.
- Inline `abstractFixedField K (SeparableClosure K) H.field` in the proof in
  place of the local `E`. Omit the source proof's local finite-dimensionality
  and fixed-field Galois instances (lines 211–215), since the direct Mathlib
  argument uses neither.
- Replace the first step's
  `H.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree.symm`
  at source line 221 by `(Subgroup.index_eq_card _).symm`. Both compare the
  same quotient cardinality with its subgroup index, using the published
  degree and quotient definitions. The other three index steps follow the
  original proof, with `E` expanded and the final intermediate field inferred.
- Extract only M330.006, retaining `noncomputable section` and
  `open ClassFormation CyclicCohomology`, and omit unrelated declarations,
  openings and notation from the original module.
- Replace the original module's broad imports with the single published
  target module. Its focused imports provide the finite abstract-field
  definitions, the concrete fixed field, `Mathlib.FieldTheory.Galois.Basic`
  and `Mathlib.FieldTheory.IsSepClosed`, including the ambient separable
  closure and the four Mathlib lemmas above. The direct quotient-cardinality
  step removes the dependency on the NYLL abstract-index helper; omitting
  the two unused instance constructions removes dependencies on their NYLL
  proofs. No other M330 unit is required by this proof.
- Use the assigned environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
  Lean 4.34.0 and the approved Mathlib pin above, in place of upstream Lean
  4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The original copyright and author header is retained verbatim. The
Apache-2.0 license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. This pair proves only the displayed degree equality
over the unchanged published objects and hypotheses.
