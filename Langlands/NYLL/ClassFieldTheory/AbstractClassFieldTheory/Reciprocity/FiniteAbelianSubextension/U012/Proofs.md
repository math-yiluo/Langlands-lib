# Induction on a finite abelian extension quotient (NYLL M296.012)

This module proves the published proposition
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extensionQuotient_inductionOnStatement`
by the protected theorem
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.extensionQuotient_inductionOn`.
Its sole import is the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Statements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has implicit `G : Type u` with `[Group G] [TopologicalSpace G]`,
implicit `K : ClosedSubgroup G`, explicit
`L : FiniteAbelianSubextension K`, implicit
`motive : L.extensionQuotient → Prop`, explicit `q : L.extensionQuotient`
and explicit
`mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)`. Its type is

```lean
L.extensionQuotient_inductionOnStatement (motive := motive) q mk
```

the target applied to the same arguments; the definition unfolds to
`motive q`.

Mathematically: let `L / K` be a finite abelian extension, represented by
closed subgroups `G_L ≤ G_K` of `G`, with Galois group
`G(L/K) = G_K / G_L`. A property of elements of `G(L/K)` that holds for the
class of every `k ∈ G_K` holds for every element of `G(L/K)`, because the
canonical projection `G_K → G(L/K)` is surjective. Only this elimination
principle is asserted; the theorem chooses no representative of `q`.

## Implemented proof

```lean
  unfold FiniteAbelianSubextension.extensionQuotient_inductionOnStatement
  exact Quotient.inductionOn' q mk
```

After `unfold` the goal is `motive q`. In the published data module
`FiniteAbelianSubextension/Definitions.lean`, `L.extensionQuotient` is the
`@[implicit_reducible]` definition
`L.toFiniteGaloisExtension.extensionQuotient`, which in
`FiniteGaloisSubextension/Definitions.lean` is by definition the quotient
group `K.toSubgroup ⧸ extensionSubgroup K L.field L.below`, that is a
`Quotient` of `K.toSubgroup` by the left coset relation. Likewise
`L.extensionQuotientMk` is by definition
`L.toFiniteGaloisExtension.extensionQuotientMk`, which is
`QuotientGroup.mk' (extensionSubgroup K L.field L.below)`, and
`L.extensionQuotientMk k` reduces to the quotient class of `k`. Mathlib's
`Quotient.inductionOn'` (`Mathlib/Data/Quot.lean`; for `q : Quotient s₁` and
a proof of the motive at every `Quotient.mk'' a`) therefore accepts `q` and
`mk` after definitional unfolding, and returns `motive q`. It is Lean core's
`Quotient.inductionOn`, which rests on `Quot.ind`: every element of a
quotient is the class of some representative.

The pinned source proves the theorem instead with
`L.toFiniteGaloisExtension.extensionQuotient_inductionOn q mk`, the
corresponding finite Galois theorem (port unit M040.016). That theorem is not
in the Library, and this proof does not need it: the direct
`Quotient.inductionOn'` route uses only the definitions imported through the
statement module. No auxiliary declaration, instance or attribute is added.
As in the source, the theorem is `protected` and keeps the implicit motive.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:119–125`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean#L119-L125)
(docstring at line 119; theorem at lines 120–125).

| Original (namespace `ClassFormation.FiniteAbelianSubextension`) | Adapted |
| --- | --- |
| Protected theorem `extensionQuotient_inductionOn`, lines 120–125 | This protected theorem, same name under `Langlands.NYLL.` |
| Binders `L`, `{motive}`, `q`, `mk`, lines 121–123 | Identical |
| Conclusion `motive q`, line 124 | `L.extensionQuotient_inductionOnStatement (motive := motive) q mk` |
| Tactic proof `exact L.toFiniteGaloisExtension.extensionQuotient_inductionOn q mk`, line 125 | `unfold` the target, then `exact Quotient.inductionOn' q mk` |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source imports; omission of the `noncomputable section`
and of the `open CyclicCohomology KummerTheory`, which the proof does not use.
The theorem docstring is the source docstring; a short module docstring is
added.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 467's dated modification record. Worker 467 wrote
this proof from the pinned original and the frozen statement module, following
the route `Quotient.inductionOn'` named in the task context by Worker 303; there
are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`.
The whole source file has SHA-256
`f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`, recomputed by
Worker 467 on 14 November 2026 UTC and equal to the value in the
[port partition](../../../../../../../notes/reuse/nyll-public-port/m289-m312.md#m296),
which lists this unit as M296.012 in module M296 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings. The theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`, the same axioms on which the target
definition itself already depends. Compilation is not acceptance: publication
under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
