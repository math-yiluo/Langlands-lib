# Compactness of the determinant-unit central intersection

Author: Worker 76.

`Langlands.CuspidalSupport.LeviDeterminantUnitCentralCompactnessTheorem F T B`
is a proposition for every prime `p`, actual field `F : PadicField.{uF} p`,
compatible realization `T : F.TopologicalData`, natural rank `n`, and ordered
positive block shape `B : Langlands.GeneralLinear.BlockShape n`. The field
universe `uF` is arbitrary. There is no positive-rank hypothesis.

The full outer parameter order is `{p : ℕ} [Fact p.Prime] (F : PadicField p)
(T : F.TopologicalData) {n : ℕ} (B : BlockShape n)`, with result `Prop`.
The proposition explicitly installs `T.topology` and states

```text
IsCompact
  (((determinantUnitSubgroup T B) ⊓ Subgroup.center (B.Levi F.Carrier) :
    Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
```

Thus it asserts compactness, as an ambient subset of the actual product Levi,
of the intersection of the blockwise determinant-unit subgroup with the actual
group center. Membership in the determinant-unit subgroup means that every
block determinant has residue-normalized absolute value one. The topology is
the product of the matrix-unit topologies induced from `T.topology`. No
compactness or centrality conclusion is assumed.

The sole import is the published
`Langlands.Representation.CuspidalSupport.DeterminantUnit`, which supplies the
actual subgroup and its defining characters. This statement is an internal
extraction of the third conjunct of
`Langlands.CuspidalSupport.LeviDeterminantUnitStructureTheorem`, published in
`Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement`.
It has exactly that conjunct's hypotheses and compactness conclusion.

The original source is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F), where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), 1–68, English translation,
Chapter II, section 3.20(a), printed page 34 (PDF page 34). That page was read.
Registered source ID: `bernstein-zelevinsky-1976-representations-gln`.
PDF SHA256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The registered original is retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

The source's `G°` is the product of the determinant-unit subgroups, and `Z` is
the center of the product Levi. Section 3.20(a) states compactness of their
intersection. Its additional congruence-subgroup containment is outside this
focused statement, as are the assertions in section 3.20(b).

The rank-zero case is the same internal extension already included in the
published structural statement: positive block sizes summing to zero force
an empty block family. The Levi is the one-element empty product, and the
intersection is its singleton subset.

This pair defines the proposition. Its proof is reserved for a separate task.
