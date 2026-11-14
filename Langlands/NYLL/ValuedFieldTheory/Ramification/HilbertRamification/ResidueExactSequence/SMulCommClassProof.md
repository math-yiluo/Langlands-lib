# NYLL M243.013: the decomposition group action commutes with the fixed subring

This module proves the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass`,
whose type is the published closed target
`decompositionFixedSubring.instSMulCommClassStatement.{u, v}` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`
(explained in the [statement Markdown](Statements.md)). It is the proof unit of the source
instance M243.013 of the
[NYLL port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

## Target

```lean
theorem decompositionFixedSubring.instSMulCommClass :
    decompositionFixedSubring.instSMulCommClassStatement.{u, v}
```

The target is the `abbrev`

```lean
∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  (A : _root_.ValuationSubring L),
  SMulCommClass (decompositionGroup K A)
    (decompositionFixedSubring K A) A
```

for an arbitrary field extension `L / K` (no Galois hypothesis) and valuation subring `A`
of `L`: for `σ` in the decomposition group, `r` in the fixed subring
`decompositionFixedSubring K A = FixedPoints.subring A (decompositionGroup K A)` (M243.001)
and `x ∈ A`, `σ • (r • x) = r • (σ • x)`. The group acts on `A` through Mathlib's
`ValuationSubring.decompositionSubgroupMulSemiringAction`
(`Mathlib/RingTheory/Valuation/RamificationGroup.lean`, line 40); the fixed subring acts on
`A` by multiplication, through the scalar action of a subring on its ambient ring.

## Implemented proof

```lean
intro K L _ _ _ A
exact instSMulCommClassSubtypeMemSubringSubring A (decompositionGroup K A)
```

After the closed telescope is introduced, the goal is, by unfolding the `abbrev`,
`SMulCommClass (decompositionGroup K A) (FixedPoints.subring A (decompositionGroup K A)) A`.
It is closed by Mathlib's anonymous instance

```lean
instance : SMulCommClass G (FixedPoints.subring B G) B :=
  inferInstanceAs (SMulCommClass G (FixedPoints.subsemiring B G) B)
```

(`Mathlib/Algebra/Algebra/Subalgebra/Operations.lean`, line 102), whose generated name is
`instSMulCommClassSubtypeMemSubringSubring` with explicit arguments `B` and `G` (the
section `variable` lines 85–86 of that file), here `B := A` (coerced to a type) and
`G := decompositionGroup K A`. The name was read from a development `#synth` of the class.
Through the subsemiring instance (line 94), Mathlib's proof is the submonoid instance
`SMulCommClass M (FixedPoints.submonoid M α) α` (`Mathlib/GroupTheory/GroupAction/Defs.lean`,
line 193), proved by `simp_rw [Submonoid.smul_def, smul_eq_mul, smul_mul', x.2 g]`: the
action of `g` is multiplicative, and `g` fixes `x`.

## Instance registration

As the task requires, the theorem is **not** registered as an instance. Because
`decompositionFixedSubring K A` is an `abbrev` for `FixedPoints.subring`, Mathlib's instance
above already supplies `SMulCommClass (decompositionGroup K A) (decompositionFixedSubring K A) A`
to instance search; registering the theorem would add a second global instance for the same
goals. The module ends with the check

```lean
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A) (decompositionFixedSubring K A) A :=
  inferInstance
```

which compiles with only the statement module imported. In a development probe, `#synth`
of this class reported `instSMulCommClassSubtypeMemSubringSubring ↥A ↥(decompositionGroup K A)`.

## Dependencies

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`: the target and, through the published M243 data module and its Mathlib
  imports, Mathlib's `Mathlib.Algebra.Algebra.Subalgebra.Operations` with the instance above.
  No other module is imported.

## Private source helper M243.011

The source instance applies the private theorem M243.011
`decompositionFixedSubring_smulCommClass`, [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 146–154](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L146-L154):

```lean
omit [IsGalois K L] in
private theorem decompositionFixedSubring_smulCommClass
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A := by
  constructor
  intro g r x
  change g • ((r : A) * x) = (r : A) * (g • x)
  rw [smul_mul', r.property g]
```

Its conclusion and telescope are exactly those of the target, so the theorem of this module
also establishes the content of M243.011. Its proof is not inlined: it is the same
computation as Mathlib's submonoid instance described above (`smul_mul'` and the fixedness
of `r`), which the task directs to reuse rather than copy. No other private source lemma is
used. The source also uses M243.011 inside the private theorem M243.015 and in the proofs of
M243.029 and M243.030 (lines 369 and 406), where the Mathlib instance equally supplies it;
those proofs are outside this module.

## Source correspondence and modifications

The source instance is [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 165–170](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L165-L170):

```lean
/-- Provides the instance `instSMulCommClass`. -/
instance decompositionFixedSubring.instSMulCommClass
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
  decompositionFixedSubring_smulCommClass (K := K) A
```

| Source | Adapted |
| --- | --- |
| `instance decompositionFixedSubring.instSMulCommClass (A) : SMulCommClass (decompositionGroup K A) (decompositionFixedSubring K A) A` | `theorem decompositionFixedSubring.instSMulCommClass : decompositionFixedSubring.instSMulCommClassStatement.{u, v}` |
| `instance` keyword | Not kept, and no `attribute [instance]` (see above) |
| Proof `decompositionFixedSubring_smulCommClass (K := K) A` (M243.011) | `intro`, then Mathlib's `instSMulCommClassSubtypeMemSubringSubring` |
| Docstring “Provides the instance `instSMulCommClass`.” | Rewritten to say which existing instance supplies it |

The following source context is not reproduced: the source imports (replaced by the
imports listed above), `noncomputable section`, and `open scoped Pointwise Topology`
(a `Prop`-valued theorem needs neither the section nor the `Topology` scope). The namespace
`RamificationTheory.HilbertRamification.ValuationSubring` gets the prefix `Langlands.NYLL`,
and `universe u v` is kept. The section variables
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` and the declaration's own
binder `(A : _root_.ValuationSubring L)` are the leading binders of the published closed
target, introduced by `intro`, with the same names, order and binder kinds. The source section variable `[IsGalois K L]` is not in the elaborated type of
this source instance (its helper is declared with `omit [IsGalois K L] in`), nor in the
target. The `example` above is new and only checks instance search.

## Development check

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), `lean_check` built this module over the
workspace's Library base `c40a01345b2f4172fa41e07ff31644b40e695003` with no errors and no
warnings. Inspection found a theorem with level parameters `u`, `v` using only the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check is not independent review
or publication.

## Attribution and license

The original copyright and author header (copyright 2026 Naganori Yamaguchi, author
“Naganori Yamaguchi (assisted by OpenAI Codex)”, released under Apache-2.0) is kept
verbatim at the top of the Lean file, followed in the same comment by Worker 173's dated
modification record. The pinned original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, retained in the registered sources
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The whole source file
(461 lines) was read; its SHA-256 is
`cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`, as recorded in the
statement Markdown. The unchanged [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are byte-identical to the retained
originals, with SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No Mathlib code is copied into this file.
Worker 121's published statement and the imported data modules are used unchanged; all
imported Library modules and their paired Markdown remain frozen.

## Scope

This module proves only M243.013 (and thereby the content of the private M243.011). It adds
no global instance and no other declaration.
