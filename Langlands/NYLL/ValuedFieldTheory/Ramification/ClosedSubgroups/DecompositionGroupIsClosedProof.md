# The decomposition group is closed in the Krull topology (NYLL M241.002)

This module proves
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosed.{u, v}`.
Its type is exactly the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosedStatement.{u, v}`,
imported from
`Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.Statements`.
This is source unit M241.002. The source's private helper M241.001
`mem_decompositionGroup_iff_apply_mem` is proved in this module as a `private` theorem; it
is not published under a public name.

## Statement proved

```lean
def decompositionGroup_isClosedStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (A : _root_.ValuationSubring L),
    IsClosed (decompositionGroup K A : Set (L ≃ₐ[K] L))
```

For every algebraic field extension `L / K` (universes `u`, `v` arbitrary; not necessarily
finite, normal or separable) and every valuation subring `A` of `L`, the decomposition group
`decompositionGroup K A = {σ ∈ L ≃ₐ[K] L | σ • A = A}` is a closed subset of `L ≃ₐ[K] L`
for Mathlib's Krull topology (`Mathlib/FieldTheory/KrullTopology.lean`).

## Private helper (M241.001)

```lean
private theorem mem_decompositionGroup_iff_apply_mem
    (A : _root_.ValuationSubring L) (sigma : L ≃ₐ[K] L) :
    sigma ∈ decompositionGroup K A ↔
      ∀ x : L, sigma x ∈ A ↔ x ∈ A
```

with section variables `(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]`
(no algebraicity hypothesis). It says that `σ` lies in the decomposition group exactly
when, for every `x : L`, `σ x ∈ A ↔ x ∈ A`. The proof is the source proof, unchanged:
membership in the decomposition group is `σ • A = A` (by `change`, since
`decompositionGroup K A` is Mathlib's `A.decompositionSubgroup K`, the stabilizer of `A`
under the pointwise action). For the forward direction, compare `σ x ∈ σ • A` with
`σ x ∈ A`, rewrite the former with Mathlib's
`ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem` to `σ⁻¹ (σ x) ∈ A`, and cancel
`σ⁻¹ (σ x) = x`. For the backward direction, prove `σ • A = A` by extensionality: after the
same rewrite, `σ⁻¹ x ∈ A ↔ x ∈ A` is the hypothesis at `σ⁻¹ x`, simplified by `simpa`.
The helper is declared `private`, so it is visible only in this file under a mangled
name; a private test importing this module confirmed that the identifier
`mem_decompositionGroup_iff_apply_mem` is unknown outside it.

## Implemented proof of M241.002

After `intro K L _ _ _ _ A`, the proof supplies the structure `IsClosed` with its field
`isOpen_compl`, using the source proof unchanged. To show the complement of the
decomposition group is open, it suffices (`isOpen_iff_mem_nhds`) that it is a neighbourhood
of each of its points `σ`.

1. Since `σ ∉ decompositionGroup K A`, the helper and `Classical.not_forall` give an
   element `x : L` with `¬ (σ x ∈ A ↔ x ∈ A)`.
2. Let `E = K⟮x⟯ = IntermediateField.adjoin K {x}`. Since `L / K` is algebraic, `x` is
   integral over `K` (`Algebra.IsIntegral.isIntegral`, an instance from algebraicity over a
   field), so `E` is finite-dimensional over `K`
   (`IntermediateField.adjoin.finiteDimensional`).
3. By `mem_nhds_iff`, it suffices to give an open set containing `σ` and contained in the
   complement. The set is the left coset `σ • E.fixingSubgroup` of the subgroup of
   automorphisms fixing `E` pointwise.
   - *Contained in the complement:* an element of the coset is `σ * g` with `g` fixing
     `E`; in particular `g x = x` (`IntermediateField.mem_fixingSubgroup_iff` and
     `IntermediateField.subset_adjoin`). If `σ * g` were in the decomposition group, the
     helper at `x` would give `σ (g x) ∈ A ↔ x ∈ A`, i.e. `σ x ∈ A ↔ x ∈ A`, contradicting
     step 1 (closed by `simpa [AlgEquiv.mul_apply, hgx]`).
   - *Open:* `E.fixingSubgroup` is open in the Krull topology because `E` is
     finite-dimensional (`IntermediateField.fixingSubgroup_isOpen`), and left translates of
     open sets are open (`IsOpen.smul`).
   - *Contains `σ`:* `σ = σ * 1` with `1 ∈ E.fixingSubgroup`.

The algebraicity hypothesis is used only in step 2. The development check reported no
errors or warnings and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. The module declares only the private helper and this theorem and adds no
instance.

## Original source and adaptation

The original is Naganori Yamaguchi (assisted by OpenAI Codex), *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean#L32-L81):
section variables at lines 32–33, the private helper M241.001 at lines 35–53 and the
theorem M241.002 at lines 55–81 (docstring 55–56, signature 57–59, proof 60–81). The
source file (217 lines) has SHA-256
`17052cbd32890aea579663eeaa851379034027b045bc2fb0daaee402f76ceef3`.

| Original | Adapted |
| --- | --- |
| Line 30 `open scoped Pointwise Topology` | Unchanged |
| Line 32 section variables | Unchanged, in a `section` enclosing only the helper |
| Line 33 `variable [Algebra.IsAlgebraic K L]` and line 35 `omit [Algebra.IsAlgebraic K L] in` | Dropped: the helper never used the hypothesis (the source omits it), and the theorem receives it from the target's binder |
| Lines 36–53, `private theorem mem_decompositionGroup_iff_apply_mem` (M241.001) | Same name, `private`, same statement and proof; a docstring is added |
| Lines 57–59, `theorem decompositionGroup_isClosed (A ...) : IsClosed ... where` | `theorem Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosed : decompositionGroup_isClosedStatement.{u, v}`; `intro K L _ _ _ _ A` introduces the section variables and `A` |
| Lines 60–81, field `isOpen_compl := ...` | The same field and proof inside `exact { isOpen_compl := ... }` |
| Import of `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup` (line 7) and `Mathlib.FieldTheory.Galois.Infinite` (line 8) | The single import of the published statement module, which imports the published M239 data module (supplying `decompositionGroup`) and `Mathlib.FieldTheory.Galois.Infinite` |
| `noncomputable section` | Omitted |

The theorem docstring is kept verbatim. Lines 83–211 (inertia and ramification closedness,
infinite Galois correspondences) are outside this unit. Worker 122 made this adaptation on
14 November 2026; the Lean header records it.

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Consumers

In the source, M241.002 is used at line 133 of `ClosedSubgroups.lean` (closedness of the
inertia group) and in `ResidueExactSequence.lean` (M243) for compactness of the
decomposition group (`decompositionGroup_compactSpace`), which feeds M243.016. Consumers
apply it as `decompositionGroup_isClosed K A`.

## Attribution and license

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0 notice
and authorship (assisted by OpenAI Codex), followed by the modification record. The
Library's [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) are unchanged (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
