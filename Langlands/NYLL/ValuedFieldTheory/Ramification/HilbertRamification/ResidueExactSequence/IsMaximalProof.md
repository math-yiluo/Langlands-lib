# NYLL M243.016: the contracted maximal ideal of the fixed subring is maximal

This module proves the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal`,
whose type is the published closed target
`decompositionFixedMaximalIdeal.instIsMaximalStatement.{u, v}` of the module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`
(explained in the [statement Markdown](Statements.md)), and registers it as a global
instance. It is the proof unit of the source instance M243.016 of the
[NYLL port inventory](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m243).

## Target

```lean
theorem decompositionFixedMaximalIdeal.instIsMaximal :
    decompositionFixedMaximalIdeal.instIsMaximalStatement.{u, v}
```

The target is the `abbrev`

```lean
∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L] (A : _root_.ValuationSubring L),
  (decompositionFixedMaximalIdeal K A).IsMaximal
```

for a Galois extension `L / K` (possibly infinite) and a valuation subring `A` of `L`.
Here `decompositionFixedMaximalIdeal K A` is the published abbreviation (M243.002)

```lean
(IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype
```

the contraction of the maximal ideal `𝔪_A` of `A` to the fixed subring
`decompositionFixedSubring K A = FixedPoints.subring A (decompositionGroup K A)` (M243.001),
where the decomposition group `decompositionGroup K A` (M239.001) acts on `A` through
Mathlib's `ValuationSubring.decompositionSubgroupMulSemiringAction`
(`Mathlib/RingTheory/Valuation/RamificationGroup.lean`, line 40). So the target says:
`𝔪_A ∩ A^D` is a maximal ideal of `A^D`.

## Implemented proof

```lean
intro K L _ _ _ _ A
exact FixedPoints.isMaximal_comap_maximalIdeal_subring
```

After the closed telescope is introduced (the anonymous binders are the field, field,
algebra and `IsGalois` instances), the goal unfolds, through the two `abbrev`s above, to

```lean
(Ideal.comap (FixedPoints.subring A (decompositionGroup K A)).subtype
  (IsLocalRing.maximalIdeal A)).IsMaximal
```

This is the conclusion of the published Library theorem

```lean
theorem FixedPoints.isMaximal_comap_maximalIdeal_subring
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [Monoid M]
    [MulSemiringAction M R] :
    (Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R)).IsMaximal
```

(`Langlands/AnthropicFLT/Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean`,
line 86) at `R := A` and `M := decompositionGroup K A`, which `exact` determines by
unification. Its instance arguments are found by instance search: the commutative ring
structure of `A`, Mathlib's `ValuationSubring.isLocalRing`
(`Mathlib/RingTheory/Valuation/ValuationSubring.lean`, line 148), the group structure of the
subgroup `decompositionGroup K A` and the action named above.

The Library theorem's own proof rewrites with `FixedPoints.maximalIdeal_subring_eq_comap`
(line 79 of the same file), which identifies the contracted ideal with the maximal ideal of
the local ring `FixedPoints.subring R M` (the instance `FixedPoints.isLocalRing_subring`,
line 50), and concludes with `IsLocalRing.maximalIdeal.isMaximal`. The identification holds
because units are detected in `R` (`FixedPoints.isUnit_subring_iff`, line 34): if a fixed
element `a` has an inverse `b` in `R`, then for every `m` the element `m • b` is also an
inverse of `a = m • a`, so `m • b = b` and the inverse lies in the fixed subring. Hence an
element of `A^D` is a non-unit of `A^D` exactly when it is a non-unit of `A`, that is,
exactly when it lies in `𝔪_A`.

The proof uses neither the Galois hypothesis nor any topology: the `[IsGalois K L]` binder
of the target is introduced and not used, so the proof in fact shows the conclusion for
every field extension. The target keeps the hypothesis because the source declaration has it
(see the statement Markdown); it is not weakened here.

## Private source theorem M243.015, established by this proof

The source instance applies the private theorem M243.015
`decompositionFixedMaximalIdeal_isMaximal`, [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 179–200](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L179-L200):

```lean
private theorem decompositionFixedMaximalIdeal_isMaximal
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  let : Algebra.IsIntegral (decompositionFixedSubring K A) A :=
    Algebra.IsInvariant.isIntegral_of_profinite
      (G := decompositionGroup K A)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (decompositionFixedSubring K A).subtype
    (fun x => Algebra.IsIntegral.isIntegral x)
    (IsLocalRing.maximalIdeal A)
```

It is stated under the source section variables of lines 39–40, including `[IsGalois K L]`,
so its elaborated type is exactly the target. The theorem proved here therefore establishes
the content of the private row M243.015, in the sense of Task 5836's private-row requirement;
no separate declaration for M243.015 is introduced, and its source proof is replaced, as the
task directs, by the Library theorem above.

The source route gives `A` the discrete topology, makes the decomposition group compact
(M243.010 `decompositionGroup_compactSpace`, lines 139–144, stated under the section
hypothesis `[IsGalois K L]`: by M241.002 `decompositionGroup_isClosed` it is a closed subset
of the compact Galois group),
makes its action continuous (M243.009 `decompositionGroup_continuousSMul`, lines 128–137,
from M243.008 `decompositionGroup_action_locallyConstant`, lines 102–126), uses the
commutation and invariance facts M243.011 and M243.012, deduces with Mathlib's
`Algebra.IsInvariant.isIntegral_of_profinite` that `A` is integral over `A^D`, and concludes
with Mathlib's `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` (the contraction of a
maximal ideal along an integral extension is maximal). The proof here does not need these
topological helpers because maximality follows from locality alone: `A` is local and `A^D`
detects units in `A`, so `𝔪_A ∩ A^D` is the maximal ideal of `A^D` with no integrality
argument. Consequently the private rows M243.008–M243.010 are neither used nor established by
this proof. In the source they are also consumed by the theorem M243.029 and the instance
M243.030 ([`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 356–392](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L356-L392) and lines 394–413), whose proofs must account for them; M243.011
and M243.012 are covered by the proofs of M243.013 and M243.014.

## Instance registration

The theorem is followed by

```lean
attribute [instance] decompositionFixedMaximalIdeal.instIsMaximal
```

which registers it as a global (not scoped or local) instance under its name in the
namespace `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`, the namespace of the adapted source instance. Because the target is an
`abbrev`, hence reducible, instance registration and instance search see through it to the
class `Ideal.IsMaximal`. As for the source instance, it applies when an `IsGalois K L`
instance is available. The module ends with the check

```lean
example (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal :=
  inferInstance
```

which compiles. In a development probe without the attribute, `inferInstance` failed for this
goal, also with all of Mathlib and the Library module above imported; so no existing instance
supplies it, and the new instance does not duplicate one. The Library theorem used here is
not an instance.

## Dependencies

- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Statements`: the target and, through the published M243 and M239 data modules, the
  definitions named above.
- `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`:
  the theorem `FixedPoints.isMaximal_comap_maximalIdeal_subring` (this published module
  imports all of Mathlib).

No private source lemma is used; M243.015 is established as explained above.

## Source correspondence and modifications

The source instance is [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`, lines 202–206](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean#L202-L206):

```lean
/-- Provides the instance `instIsMaximal`. -/
instance decompositionFixedMaximalIdeal.instIsMaximal
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal :=
  decompositionFixedMaximalIdeal_isMaximal (K := K) A
```

| Source | Adapted |
| --- | --- |
| `instance decompositionFixedMaximalIdeal.instIsMaximal (A) : (decompositionFixedMaximalIdeal K A).IsMaximal` | `theorem decompositionFixedMaximalIdeal.instIsMaximal : decompositionFixedMaximalIdeal.instIsMaximalStatement.{u, v}` followed by `attribute [instance] decompositionFixedMaximalIdeal.instIsMaximal` |
| Proof `decompositionFixedMaximalIdeal_isMaximal (K := K) A` (M243.015, profinite-integrality route) | `intro`, then the Library theorem `FixedPoints.isMaximal_comap_maximalIdeal_subring` |
| Docstring “Provides the instance `instIsMaximal`.” | Kept |

The following source context is not reproduced: the source imports (replaced by the
imports listed above), `noncomputable section`, and `open scoped Pointwise Topology`
(a `Prop`-valued theorem needs neither the section nor the `Topology` scope). The namespace
`RamificationTheory.HilbertRamification.ValuationSubring` gets the prefix `Langlands.NYLL`,
and `universe u v` is kept. The section variables
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]` and the declaration's own
binder `(A : _root_.ValuationSubring L)` are the leading binders of the published closed
target, introduced by `intro`, with the same names, order and binder kinds. The source section variable `[IsGalois K L]` is in the elaborated type of this
source instance and is the sixth binder of the target, introduced by the same `intro`. The
`example` above is new and only checks instance search.

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
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The Library theorem used here comes from the Anthropic FLT port (Apache-2.0), credited in its own module; none of its code is copied here.
Worker 121's published statement and the imported data modules are used unchanged; all
imported Library modules and their paired Markdown remain frozen.

## Scope

This module proves only M243.016 (and with it the content of the private M243.015). Besides
the theorem and its instance attribute it adds no declaration. It does not prove that the
contracted ideal equals the maximal ideal of `A^D` (M243.017) or any other row of M243.
