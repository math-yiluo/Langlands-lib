# Discreteness of the native norm quotient (M257.008)

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.normQuotient_discreteStatement`
by the theorem `Langlands.NYLL.LocalClassFieldTheory.normQuotient_discrete`.
For every finite Galois extension `L/K` of a nonarchimedean local field `K`,
the quotient topology on the actual norm quotient `NormQuotient K L` is
discrete.

## Target and exact parameters

The theorem takes exactly the target's telescope, in the same order:

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
```

and its conclusion is `normQuotient_discreteStatement K L`, which unfolds to
`DiscreteTopology (NormQuotient K L)`. Both fields are in `Type 0`, as in the
source. There is no topology, valuation or normed structure on `L`, no
abelian-Galois premise, and no openness or finite-index hypothesis.

`NormQuotient K L` is `Kˣ ⧸ localNormSubgroup K L`, where
`localNormSubgroup K L` is the range of the actual field norm on units
(published `NormQuotient.U001`/`U002` definitions). Its topology is the
published source-local instance `Langlands.NYLL.PortInternal.M257.d001`
(`TopologicalReciprocity.U001.Definitions`), which is Mathlib's quotient-group
topology on `Kˣ ⧸ localNormSubgroup K L` for the native unit-group topology of
`Kˣ` induced from the given topology on `K`. The file enables that instance
locally with `attribute [local instance]`, exactly as the target module does,
so the target is read with the same topology; no global instance and no
replacement discrete topology is introduced.

## Implemented proof

```lean
  let N := localNormSubgroup K L
  change DiscreteTopology (Kˣ ⧸ N)
  apply QuotientGroup.discreteTopology
  exact localNormSubgroup_isOpen K L
```

1. `change` unfolds the statement and `NormQuotient K L` definitionally to
   discreteness of `Kˣ ⧸ N` with its quotient topology (the `d001` instance is
   by definition that quotient topology).
2. Mathlib's `QuotientGroup.discreteTopology` (in
   `Mathlib.Topology.Algebra.Group.Quotient`) states that for a topological
   group `G` and subgroup `N`, if `N` is open in `G` then `G ⧸ N` is discrete.
   Here `G = Kˣ` with its native units topology; its topological-group
   structure is Mathlib's instance `IsTopologicalGroup αˣ` for `[ContinuousMul α]`
   (`Mathlib.Topology.Algebra.Group.Units`), found by instance search from the
   given local-field topology on `K`, in which multiplication is continuous.
3. The remaining goal `IsOpen (N : Set Kˣ)` is closed by the published
   M257.007 theorem `Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_isOpen`
   (`TopologicalReciprocity.U007.Proofs`), applied to the same `K L` with the
   same instances. Its type is `localNormSubgroup_isOpenStatement K L`, which
   unfolds definitionally to `IsOpen (localNormSubgroup K L : Set Kˣ)`; the
   `let`-bound `N` is likewise definitionally `localNormSubgroup K L`, so
   `exact` closes the goal.

The mathematical content is therefore entirely the openness of the norm
subgroup; discreteness of the quotient by an open subgroup is general topology.

## Dependencies

Direct imports:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Statements`
  (the unchanged target, which also supplies `d001`, `localNormSubgroup` and
  `NormQuotient`);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U007.Proofs`
  (the published exact openness proof `localNormSubgroup_isOpen`).

Used declarations: `Langlands.NYLL.PortInternal.M257.d001`,
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup`,
`Langlands.NYLL.LocalFieldTheory.NormQuotient`,
`Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_isOpen`, and Mathlib's
`QuotientGroup.discreteTopology`. No new auxiliary declaration, instance,
hypothesis or axiom is introduced, and neither the target pair nor anything it
imports is modified.

## Source correspondence and changes

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`
(whole-file SHA-256
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`),
lines 333–343: docstring at 333, `theorem normQuotient_discrete` at 334,
binders at 335–338, conclusion `DiscreteTopology (NormQuotient K L)` at 339
and the four-line proof at 340–343. The source's local instance
`normQuotientTopologicalSpace` (lines 36–41) is the published `d001`, and the
source theorem `LocalClassFieldTheory.localNormSubgroup_isOpen` (lines
220–331) corresponds to the published M257.007 theorem of the same adapted
name used in step 3. That published proof has the source's statement but a
different route from the source's (Worker 65's U007.Proofs uses an element of
nonzero trace, the norm as a determinant and Newton's method over the
valuation ring of `K`, instead of spectral-norm structures on `L` and the
M257.006 compatible openness theorem); this file uses only its statement.
The retained source is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Original in `LocalClassFieldTheory` | Adapted |
| --- | --- |
| Asserted type of `normQuotient_discrete` | Published `Langlands.NYLL.LocalClassFieldTheory.normQuotient_discreteStatement` (U006.Statements) |
| Proof `normQuotient_discrete` | This theorem, same adapted name, in U008.Proofs |
| `localNormSubgroup_isOpen` | Published M257.007 proof in U007.Proofs |
| local instance `normQuotientTopologicalSpace` | Published `Langlands.NYLL.PortInternal.M257.d001`, enabled locally |

Changes: the namespace is prefixed with `Langlands.NYLL`; the conclusion is
written as the published statement applied to `K L` (definitionally the
original conclusion); the source imports are replaced by the two published
modules above; the source's `noncomputable section`, the unused universe of
the enclosing section and the other declarations of the file are omitted.
The first three proof lines are the original ones. The original last line
`simpa only [N] using localNormSubgroup_isOpen K L` is replaced by
`exact localNormSubgroup_isOpen K L`: the published openness theorem's type is
its `Statement` definition, which `simpa only [N]` does not unfold, whereas
`exact` checks the definitional equality directly. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m257)
places this unit at M257.008 after M257.007.END.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 66's dated modification
record. The unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained in
`licenses/NYLL/`; their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). Development compilation
is separate from acceptance.

This proof covers only M257.008. It discharges no host class-formation, Tate,
cup-product or transfer target, and it constructs no reciprocity map; the
topological reciprocity results later in the source file remain separate work.
