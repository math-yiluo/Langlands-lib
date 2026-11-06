# Structure of the actual centralizer of a maximal split torus

Author: Worker 1072 (task `0becf90b-3422-4e36-bbc1-55342700202d`).

```lean
theorem Langlands.BruhatTits.Cartan.actualCentralizerStructure :
    ActualCentralizerStructureStatement.{u}
```

This proves the statement in
[`ActualCentralizerStructureStatement`](ActualCentralizerStructureStatement.md),
at an arbitrary universe `u`. Let `F` be a field, `G` a connected reductive
group scheme over `Spec F`, `i : S ⟶ G` a maximal split torus, `j : Z ⟶ G` a
closed subgroup representing the centralizer of `i`, and `s : S ⟶ Z` with
`s ≫ j = i`. Then `Z` is connected reductive and `s` is the split component
of `Z`.

## Proof

The proof is the single term

```lean
actualCentralizerStructure_of genericCentralizer dynamicCentralizerReductive
```

- `actualCentralizerStructure_of`, in
  [`ActualCentralizerSplitComponent`](ActualCentralizerSplitComponent.md), is
  submitted with this proof. It proves the split-component half outright. It
  derives the connected-reductive half from `GenericCentralizerStatement` and
  `DynamicCentralizerReductiveStatement`, which it takes as hypotheses.
- `Langlands.GroupScheme.genericCentralizer`, in the Library module
  `Langlands.GroupScheme.Rational.GenericCentralizerProof`, proves
  `GenericCentralizerStatement`: the centralizer of a split torus equals the
  dynamic centralizer of a generic cocharacter of it.
- `Langlands.GroupScheme.dynamicCentralizerReductive`, in the Library module
  `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`, proves
  `DynamicCentralizerReductiveStatement`: the represented dynamic centralizer
  of a cocharacter of a connected reductive group is connected reductive.

## Provenance

The route follows Milne, *Algebraic Groups* (2017), Corollary 17.59 (printed
p.371): the centralizer of a torus is the centralizer of a sufficiently
general cocharacter of it, and centralizers of cocharacters of connected
reductive groups are connected reductive. The split-component argument is the
derivation recorded in the target's Markdown. The companion Markdown gives the
details.
