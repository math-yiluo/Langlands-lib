# NYLL M296.013: extensionality of finite abelian subextensions

Worker 468, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extStatement`
under the theorem name
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.ext`.
The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Statements`.
The published statement and the definitions it imports are unchanged.

The theorem is declared as

```lean
theorem ext {L₁ L₂ : FiniteAbelianSubextension K}
    (h : L₁.field = L₂.field) : extStatement h
```

with the section variables `{G : Type u} [Group G] [TopologicalSpace G]`
and `{K : ClosedSubgroup G}`. Its parameters are those of `extStatement`,
in the same order and with the same binder kinds:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `G : Type u` | implicit | The ambient group (universe parameter `u`) |
| `[Group G]`, `[TopologicalSpace G]` | instance | Its group structure and topology |
| `K : ClosedSubgroup G` | implicit | The closed subgroup representing the base field |
| `L₁ L₂ : FiniteAbelianSubextension K` | implicit | Two finite abelian subextension packages over `K` |
| `h : L₁.field = L₂.field` | explicit | The two packages have the same closed top-field subgroup |

By its definition in `FiniteAbelianSubextension/Statements.lean`
(lines 58–63), `extStatement h` is the equation `L₁ = L₂`. The theorem
therefore says that a finite abelian subextension package is determined
by its top-field subgroup. No hypothesis, universe parameter or instance
argument is added.

## Implemented proof

```lean
  cases L₁ with
  | mk L₁ h₁ =>
      cases L₂ with
      | mk L₂ h₂ =>
          cases L₁ with
          | mk F₁ b₁ n₁ f₁ =>
              cases L₂ with
              | mk F₂ b₂ n₂ f₂ =>
                  dsimp only [field] at h
                  cases h
                  rfl
```

The published structures used are:

- `FiniteAbelianSubextension K` (`FiniteAbelianSubextension/Definitions.lean`,
  lines 37–41), with fields `toFiniteGaloisExtension :
  FiniteGaloisSubextension K` and the proposition `commutative :
  IsMulCommutative toFiniteGaloisExtension.extensionQuotient`. Its
  abbreviation `field` (lines 48–49) is `L.toFiniteGaloisExtension.field`.
- `FiniteGaloisSubextension K` (`FiniteGaloisSubextension/Definitions.lean`,
  lines 37–45), with data field `field : ClosedSubgroup G` and three
  proposition fields: `below` (containment in `K`), `normal` (normality of
  the extension subgroup) and `finite` (finiteness of the relative
  quotient).

The proof runs as follows.

1. The first two `cases` split `L₁` and `L₂` into their underlying finite
   Galois packages and commutativity proofs `h₁`, `h₂`. The next two split
   those Galois packages into top-field subgroups `F₁`, `F₂` and the proofs
   `b₁ n₁ f₁`, `b₂ n₂ f₂` of the three proposition fields. Each `cases`
   generalizes the hypothesis `h` and the goal, which depend on the package.
2. `dsimp only [field] at h` unfolds the abbreviation `field` and reduces
   the structure projections, so `h` becomes `F₁ = F₂`.
3. `cases h` substitutes `F₁` for the local variable `F₂` everywhere.
4. The goal is now `extStatement` of two anonymous-constructor packages with
   the same top-field subgroup `F₁`. All their remaining fields — `b`, `n`,
   `f` and the commutativity proofs — are proofs of propositions
   (`Subgroup.Normal`, `Finite` and `IsMulCommutative` are all
   `Prop`-valued). By definitional proof irrelevance the two packages are
   definitionally equal, and `rfl`, which unfolds `extStatement` to the
   equation, closes the goal.

The proof uses only Lean core tactics and the definitional behaviour of
these structures. It invokes no other NYLL theorem. A development check
inspection reports the axioms `propext`, `Classical.choice` and
`Quot.sound` only.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`,
lines 127–142 (M296.013): docstring at lines 127–128, `@[ext]` at line 129,
signature at lines 130–131, proof at lines 132–142. The section variables
are at lines 40 and 52 of the same file, and its `open` line is line 34. The source structures are at
lines 44–48 of that file and at lines 34–42 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`.
The source file SHA-256 is
`f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`.

The retained original snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
registered source `external-lean-reuse-snapshots-2026-10-21`. The
attribution and notice files are in the registered supplement
`nyll-classfieldtheory-fbd320cd-supplement`.

| Source declaration | Published proof declaration |
| --- | --- |
| `ClassFormation.FiniteAbelianSubextension.ext` | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.ext` |

Modifications:

- The namespace is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the single published statement
  module. The source's `open CyclicCohomology KummerTheory` is omitted;
  the proof uses neither namespace.
- The stated type `L₁ = L₂` is replaced by the published target
  `extStatement h`, which is that equation by definition.
- The source `@[ext]` attribute is omitted. Lean's `ext` attribute
  accepts only theorems whose stated type is syntactically an equation
  `x = y` between variables. A development check with the attribute kept
  failed with the error that the theorem proves `extStatement ?h`.
  Consequently this pair does not register an `ext` lemma for the `ext`
  tactic and does not generate the source's derived `ext_iff` theorem.
  The published target does not include them; the
  published M008.021 proof `Langlands.NYLL.ClassFormation.ZHat.ext`
  omits its source `@[ext]` attribute in the same way.
- The proof body is the source's, unchanged.
- No other source declaration is reproduced, and no public helper or
  instance is introduced.

The original copyright, Apache-2.0 license statement and author header are
preserved in the Lean file. The inherited `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This pair proves M296.013 only. It does not prove the other M296 targets
`extensionQuotientMk_applyStatement` (M296.011) or
`extensionQuotient_inductionOnStatement` (M296.012), the partial order
on finite abelian subextensions, or any reciprocity result.

## Development validation

Lean service check `bd685de5-cb94-4a86-b9a0-c2a079e2faf2` built the module
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` without errors or
warnings. Its declaration inspection reports universe parameter `u` and
only the axioms `propext`, `Classical.choice` and `Quot.sound`. Check
`6b266a14-2356-4307-8136-b256c5242a6d` recorded the failure of the kept
`@[ext]` attribute. Independent review, exact-target validation and
publication remain separate.
