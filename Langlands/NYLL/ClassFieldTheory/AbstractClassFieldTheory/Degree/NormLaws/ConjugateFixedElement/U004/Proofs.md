# The coercion of the right conjugate of a fixed element

This module proves the theorem
`Langlands.NYLL.ClassFormation.conjugateFixedElement_coe`, the proof phase of
M026.004 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m026).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.conjugateFixedElement_coeStatement` applied to the
theorem's parameters:

```lean
theorem conjugateFixedElement_coe [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    conjugateFixedElement_coeStatement A K σ a
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, where `IntegralRepGroupType` is the universe-zero type of acting groups that Mathlib's `Rep ℤ G` requires. The theorem takes `[ContinuousMul G]`, `A`, `K`, `σ` and `a`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Statements`, the target is the proposition

```lean
((conjugateFixedElement A K σ a :
    ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
  A.ρ σ⁻¹ a.1
```

Here `A : Rep ℤ G` is an integral representation of `G`, `K : ClosedSubgroup G` is an abstract field, `σ : G`, and `a : ambientFixedAddSubgroup A K`; `ambientFixedAddSubgroup A K` (M023.001) is the additive subgroup of `A.V` of the elements fixed by every element of `K`. `conjugateClosedSubgroup K σ` (M026.001) is the conjugate abstract field `K^σ`, whose subgroup is `σ⁻¹ K σ` (the construction writes the action on the right), and `conjugateFixedElement A K σ a` (M026.003) is the right conjugate `a^σ`, the element `A.ρ σ⁻¹ a.1` regarded as fixed by `K^σ`. The target says that the underlying element of `A.V` of the right conjugate is `A.ρ σ⁻¹ a.1`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Statements`, which defines the target and imports `conjugateFixedElement` (M026.003), `conjugateClosedSubgroup` (M026.001) and `ambientFixedAddSubgroup` (M023.001).

The module opens `KummerTheory`, as the source does, for `ambientFixedAddSubgroup`; the source's `open CyclicCohomology` and `open scoped BigOperators Pointwise` are not needed, since none of their names or notation occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof `rfl`: by its definition (M026.003), `conjugateFixedElement A K σ a` is the subtype element with underlying value `A.ρ σ⁻¹ a.1`, so both sides are definitionally equal.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, lines 79–90](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean#L79-L90):
the docstring at lines 79–82, the attribute at line 83 and the theorem at lines 84–90. It lies in `namespace ClassFormation` (line 16), with `open KummerTheory` (line 18) and `open CyclicCohomology` (line 20), its `noncomputable section` (line 24), `open scoped BigOperators Pointwise` (line 26) and the variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 29). The source is:

```lean
/--
Establishes the identity `((conjugateFixedElement A K σ a : ambientFixedAddSubgroup A
(conjugateClosedSubgroup K σ)) : A.V) = A.ρ σ⁻¹ a.1`.
-/
@[simp]
theorem conjugateFixedElement_coe [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
      A.ρ σ⁻¹ a.1 :=
  rfl
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`;
its SHA-256 is `985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `conjugateFixedElement_coeStatement A K σ a` as its type, and begin the proof with `show` stating it unfolded; the source's term proof `rfl` is kept as the tactic `rfl`;
- omit the `@[simp]` attribute (the theorem's type is the published `...Statement` proposition, not an equation), the source's `open CyclicCohomology` and `open scoped BigOperators Pointwise`, and all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M026.004. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
