# Splitting of trigonalizable groups (Milne 16.26), proof

Author: Worker 60 (Task 7805). Module
`Langlands.GroupScheme.Trigonalizable.ExtensionSplitProof`.

`Langlands.GroupScheme.trigonalizableExtensionSplit` proves the unchanged
[`TrigonalizableExtensionSplitStatement.{u}`](ExtensionSplitStatement.md)
in every universe `u`. This is Milne, *Algebraic Groups* (2017), Theorem
16.26 (printed p.332), in all three cases. Let `G` be affine and locally of
finite type over a field `k`, with a closed normal unipotent subgroup
`i : U ⟶ G` and an fppf quotient `q : G ⟶ D(Λ)` by it onto a diagonalizable
group with finitely generated character group `Λ`. Then `q` has a
group-scheme section `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙 D(Λ)` in each of the
cases

- (a) `k` is algebraically closed;
- (b) `k` is perfect and `U` is smooth and connected;
- (c) `k` is perfect and `D(Λ)` is connected.

[The statement's Markdown](ExtensionSplitStatement.md) compares it with the
source.

## Implemented proof

The proof is the one-line term

```
trigonalizableExtensionSplit_of_etale etaleDiagonalizableExtensionSplit.{u}
```

and it combines two published theorems.

- `Langlands.GroupScheme.trigonalizableExtensionSplit_of_etale`, from
  [`ExtensionSplitPerfectSmooth`](ExtensionSplitPerfectSmooth.md), proves
  `TrigonalizableExtensionSplitStatement.{u}` from the single premise
  `EtaleDiagonalizableExtensionSplitStatement.{u}`. It splits on the three
  cases.
  - Case (a) uses `exists_section_of_isAlgClosed` from
    [`ExtensionSplitAlgClosed`](ExtensionSplitAlgClosed.md) and needs no
    premise.
  - Case (c) uses `exists_section_of_perfect_of_connected` from
    [`ExtensionSplitPerfectConnected`](ExtensionSplitPerfectConnected.md)
    and needs no premise.
  - Case (b) uses `exists_section_of_perfect_of_smooth`. In characteristic
    zero it splits the character-linear kernel tower of `q` directly. In
    characteristic `p > 0` it first applies the premise over the
    prime-to-`p` finite étale closed subgroup `D(Λ ⧸ K) ⊆ D(Λ)`. It then
    extends that section step by step up the kernel tower of `q`. Over the
    perfect field `k`, the correction equation of each step can be solved
    compatibly with the section already chosen (`RelativeSolvable`, from
    [`PrimeToPart`](PrimeToPart.md)).
- `Langlands.GroupScheme.etaleDiagonalizableExtensionSplit`, from
  [`EtaleExtensionSplitProof`](EtaleExtensionSplitProof.md) (Task 7944),
  proves that premise
  ([`EtaleDiagonalizableExtensionSplitStatement`](EtaleExtensionSplitStatement.md),
  SGA 3 XVII, Lemme 5.2.3 i) c), for a finite étale `D(Λ)` and a smooth
  connected unipotent kernel over a perfect field).

Both theorems are universe-polymorphic in `u`, and the premise is used at
the same universe `u` as the target. The module adds no other declaration
and leaves the statement's Lean/Markdown pair and the pairs it imports
unchanged.
