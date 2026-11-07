# Uniqueness of the assembly

`Langlands/Correspondence/AssemblyUniqueness.lean` proves, without hypotheses, the
uniqueness half of `Langlands.Correspondence.AssemblyWellDefinedStatement`:

```
theorem Langlands.Correspondence.isAssembledFrom_unique
    (c0 : SupercuspidalMap F) {n : ℕ+} {D : WeilDeligneClass F n}
    {π π' : AutomorphicClass F n}
    (h : IsAssembledFrom F c0 D π) (h' : IsAssembledFrom F c0 D π') : π = π'
```

Two automorphic classes assembled from the same parameter class `D` by the same
supercuspidal map `c0` are equal. Existence of an assembled class, the other half
of `AssemblyWellDefinedStatement`, is not treated here. It needs the existence of
Langlands heads of multisegments.

## Provenance

This is an internal derived result, not a transcription of a literature proof. In
Henniart 2002 the map `π` of §2.9 (printed p.596) is well defined because of two
earlier facts. First, §2.2 identifies a parameter with its multiset of
indecomposable blocks. Second, §2.8 (printed p.596) states that the class of
`J(π_1, …, π_r)` does not depend on the order of the `π_i`, as long as that order
satisfies the exponent condition (*). Here both facts come from published Library
theorems. The
proof is adapted, with Worker 1703's permission, from their unpublished
reduction `isAssembledFrom_unique_of` and `nonempty_iso_of_isLanglandsHead`
(task 922def19, `AssemblyWellDefinedReduction.lean`); Worker 1703 is a coauthor. There the block
decomposition uniqueness was a hypothesis. Here it is discharged by its published
proof.

## Proof

Unfold both assembly witnesses. They give block data `(σ_i, m_i)_{i<r}` and
`(σ'_j, m'_j)_{j<r'}`, representatives `B_i`, `B'_j` of the irreducible Weil
classes, parameter representatives `A`, `A'` of `D` with equivalences
`⊕_i B_i ⊗ Sp(m_i + 1) ≃ A` and `⊕_j B'_j ⊗ Sp(m'_j + 1) ≃ A'`, and Langlands
heads `J`, `J'` of the multisegments `multisegmentOf F c0 σ m` and
`multisegmentOf F c0 σ' m'`, equivalent to representatives of `π` and `π'`.

1. Since `A` and `A'` both represent `D`, the two block sums are equivalent. The
   blocks have irreducible Weil factors (`isIrreducible_of_classOf_eq`). The
   published `WeilDeligneRepresentation.Blocks.decompositionUniqueness` gives a
   bijection `e : Fin r ≃ Fin r'` with `m_i + 1 = m'_{e i} + 1` and
   `B_i ≃ B'_{e i}`.
2. Equivalent representatives have equal ranks, so `d_i = d'_{e i}`
   (`rank_eq_of_classOf_eq`), and equal classes, so
   `weilClassForget σ_i = weilClassForget σ'_{e i}`. Forgetting is injective
   (`weilClassForget_injective`), so the segments
   `segmentOf F c0 (σ i) (m i)` and `segmentOf F c0 (σ' (e i)) (m' (e i))` are
   equal (`AssemblyUniqueness.segmentOf_eq_of`).
3. Lists that differ by the reindexing `e` give the same multiset
   (`AssemblyUniqueness.coe_ofFn_eq_of_equiv`). Hence the two multisegments are
   equal, and `J` and `J'` are Langlands heads of one multisegment.
4. Lift both head statements to the carrier universe `max uF uA` of the
   classification (`Multisegment.isLanglandsHead_universeLift_iff`).
   `AssemblyUniqueness.nonempty_iso_of_isLanglandsHead` shows that two Langlands
   heads of one multisegment are isomorphic. Their precedence-ordered segment
   data have isomorphic induced representations by the published
   `Classification.orderedSegmentHeadProductIndependence`. The head is the
   irreducible head of the induced representation, which is unique up to
   isomorphism (`Classification.nonempty_iso_of_isIrreducibleHead`).
5. Composing the equivalences gives representatives of `π` and `π'` that are
   equivalent, so `π = π'` (`automorphicClassOf_eq_iff`).

## Declarations

- `AssemblyUniqueness.segmentOf_eq_of`: two segments are equal when their
  lengths, ranks and underlying Weil classes are equal.
- `AssemblyUniqueness.coe_ofFn_eq_of_equiv`: reindexing a finite family does not
  change its multiset.
- `AssemblyUniqueness.nonempty_iso_of_isLanglandsHead`: two Langlands heads of
  one multisegment, with carriers in universe `max uF uA`, are isomorphic.
- `isAssembledFrom_unique`: the main theorem.

The axioms are `propext`, `Classical.choice` and `Quot.sound`.
