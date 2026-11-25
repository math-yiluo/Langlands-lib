# The quasi-split envelope from Borel–Tits 7.2 and the nonmultipliable coroot span

The module proves one theorem,

```
theorem simplyConnectedQuasiSplitEnvelope_of_maximalSplitSubgroup
    (hBT : MaximalSplitSubgroupStatement.{u})
    (hHL : NonmultipliableCorootSpanStatement.{u}) :
    SimplyConnectedQuasiSplitEnvelopeStatement.{u}
```

It proves neither premise. Together with proofs of
[`MaximalSplitSubgroupStatement`](../Rational/MaximalSplitSubgroupStatement.md) (Borel–Tits
1965, 7.2) and [`NonmultipliableCorootSpanStatement`](NonmultipliableCorootSpanStatement.md)
(Borel–Tits 1972, 4.3–4.4) it proves the target
[`SimplyConnectedQuasiSplitEnvelopeStatement`](QuasiSplitEnvelopeStatement.md). This is the
route of the target's Markdown: take `H = F` from 7.2 and use Humphreys's corollary (1972, 4.6).
The intermediate steps are internal derived glue using published Library theorems.

## Proof

Let `G` be simply connected and `i : S ⟶ G` a maximal split torus. `G` is connected
reductive (`hG.isSemisimple.isConnectedReductive`).

1. `hBT` gives `F` connected reductive, a closed subgroup `j : F ⟶ G` and `f : S ⟶ F` with
   `f ≫ j = i`, `IsMaximalTorus f` and `roots f` equal to the nonmultipliable roots of `i`.
2. `S` is a split torus (`hi.1.1`). `rootDatumExistence` gives a root datum `P` of `f` on the
   lattices of `S` (`IsRootDatumOf f P`).
3. `hHL` applies to `P`: its pairing clause is `hP.1`; its roots are `roots f` by `hP.2.1`,
   which are the nonmultipliable roots of `i` by step 1; for each reflection, `hP.2.2` gives a
   rational point `n` of `F` normalizing `f`, and `IsNormalizingPoint.comp_hom` with
   `f ≫ j = i` makes `n ≫ j` a rational point of `G` normalizing `i` through the same
   automorphism of `S`. Hence `P.corootSpan ℤ = ⊤`.
4. The quotient of the cocharacter lattice by `⊤` is finite, so the coroot form of
   `splitSemisimpleRootDatum` gives `IsSemisimple F`.
5. `splitCorootSpanSimplyConnected` (the coroot criterion) gives `IsSimplyConnected F`.
6. `maximalTorusCentralizer` identifies the centralizer of the maximal torus `f` with its
   range, so `f` represents `torusCentralizer f` (`f` is a closed immersion, hence a
   monomorphism). `IsSplitTorus.isQuasiSplit_of_torusCentralizer` then gives
   `IsQuasiSplit F`.
7. `IsMaximalSplitTorus.of_comp` with the closed subgroup `j` and `f ≫ j = i` gives
   `IsMaximalSplitTorus f`.

The witnesses are `H = F`, `j`, `f`.
