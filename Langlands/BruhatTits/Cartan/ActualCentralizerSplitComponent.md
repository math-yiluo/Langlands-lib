# The split component of the represented centralizer of a maximal split torus

Author: Worker 1072 (task `0becf90b-3422-4e36-bbc1-55342700202d`).

This module proves the split-component half of
`Langlands.BruhatTits.Cartan.ActualCentralizerStructureStatement` (in
[`ActualCentralizerStructureStatement`](ActualCentralizerStructureStatement.md))
outright. It reduces the connected-reductive half to two Library statements
that it takes as hypotheses: `GenericCentralizerStatement` and
`DynamicCentralizerReductiveStatement`. It proves neither of them.

Throughout, `F` is a field, `G` and `Z` are group schemes over `Spec F`, `S` is
a commutative group scheme over `Spec F`, `i : S.toGrp ⟶ G` and `j : Z ⟶ G`.

## Closed subgroups and composition

```lean
theorem IsClosedSubgroup.of_comp {H} {f : H ⟶ Z}
    (hj : IsClosedSubgroup j) (hf : IsClosedSubgroup (f ≫ j)) : IsClosedSubgroup f
theorem IsClosedSubgroup.comp' {H} {f : H ⟶ Z}
    (hf : IsClosedSubgroup f) (hj : IsClosedSubgroup j) : IsClosedSubgroup (f ≫ j)
```

`IsClosedSubgroup f` means that the underlying scheme morphism of `f` is a
closed immersion. The first lemma is Mathlib's
`IsClosedImmersion.of_comp_isClosedImmersion`; the second is the composition
instance for closed immersions.

## Centrality inside the centralizer

```lean
theorem isCentral_of_torusCentralizer (hZ : (torusCentralizer i).IsRepresentedBy j)
    {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) : IsCentral s
```

Let `x` be a point of `S` over a test scheme and `h` a point of `Z` over a
refinement of it. Because `j` represents `torusCentralizer i`, the point
`h ≫ j` of `G` lies in the centralizer, so it commutes with the image under
`i = s ≫ j` of the pulled-back point of `S`. Both products in `Z` map to the
same point of `G` under `j`. Since `j` is a monomorphism (the first component
of `IsRepresentedBy`), the two products are equal in `Z`.

## Split subtorus and split component

```lean
theorem isSplitSubtorus_of_torusCentralizer (hi : IsMaximalSplitTorus i)
    (hj : IsClosedSubgroup j) {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) : IsSplitSubtorus s
theorem isSplitComponent_of_torusCentralizer (hi : IsMaximalSplitTorus i)
    (hj : IsClosedSubgroup j) (hZ : (torusCentralizer i).IsRepresentedBy j)
    {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) : IsSplitComponent s
```

`S` is a split torus because `i` is a split subtorus of `G`. The morphism `s`
is a closed subgroup by `IsClosedSubgroup.of_comp`, since `s ≫ j = i` and `j`
are closed subgroups. Together with `isCentral_of_torusCentralizer` this gives
`IsCentralSplitTorus s`.

For maximality, let `i' : A' ⟶ Z` be a central split torus of `Z` and
`f : S ⟶ A'` with `f ≫ i' = s`. Then `i' ≫ j` is a split subtorus of `G`, by
`IsClosedSubgroup.comp'`, and `f ≫ (i' ≫ j) = s ≫ j = i`. The maximality of
`i` among split subtori of `G` then gives that `f` is an isomorphism. The
centrality of `i'` is not used. None of these lemmas uses reductivity of `G`.

## Connected reductivity, conditionally

```lean
theorem isConnectedReductive_of_torusCentralizer (hi : IsMaximalSplitTorus i)
    (hgen : GenericCentralizerStatement.{u})
    (hdyn : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (hj : IsClosedSubgroup j)
    (hZ : (torusCentralizer i).IsRepresentedBy j) : IsConnectedReductive Z
```

The published `IsSplitTorus.exists_genericCocharacter` (in
`Langlands.GroupScheme.Rational.GenericCocharacter`) gives a cocharacter
`ν` of `S` with `IsGenericCocharacter i ν`. The hypothesis `hgen`, applied to
`G`, `S`, `i` and `ν`, identifies the dynamic centralizer
`Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)` with
`torusCentralizer i`. So `j` represents that dynamic centralizer, and the
hypothesis `hdyn`, applied to the cocharacter `CommGroupScheme.groupHom ν ≫ i`
of `G` and to `j`, gives `IsConnectedReductive Z`.

```lean
theorem actualCentralizerStructure_of
    (hgen : GenericCentralizerStatement.{u})
    (hdyn : DynamicCentralizerReductiveStatement.{u}) :
    ActualCentralizerStructureStatement.{u}
```

This pairs the two results above.
[`ActualCentralizerStructureProof`](ActualCentralizerStructureProof.md)
applies it to the Library proofs of `GenericCentralizerStatement` and
`DynamicCentralizerReductiveStatement` to prove the target.

## Provenance

The split-component argument is the derivation recorded in the target's
Markdown: centrality comes from the all-test-scheme commutation condition, and
maximality from split maximality of `S` in `G` through the closed immersion
`j`. The reductivity route follows Milne, *Algebraic Groups* (2017),
Corollary 17.59 (printed p.371): the centralizer of a torus equals the
centralizer of a sufficiently general cocharacter of it, and centralizers of
cocharacters of connected reductive groups are connected reductive. Here these
two inputs are the two hypothesis statements.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
