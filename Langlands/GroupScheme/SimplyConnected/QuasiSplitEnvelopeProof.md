# Proof of the quasi-split simply connected envelope

Author: Worker 162 (Task 7779).

The module proves the Library proposition
[`SimplyConnectedQuasiSplitEnvelopeStatement`](QuasiSplitEnvelopeStatement.md):

```
theorem simplyConnectedQuasiSplitEnvelope : SimplyConnectedQuasiSplitEnvelopeStatement.{u}
```

Let `k` be a field, `G` a simply connected `k`-group scheme and `i : S ⟶ G` a maximal split
torus. Then there are a closed subgroup `j : H ⟶ G` with `H` simply connected and quasi-split,
and `f : S ⟶ H` with `f ≫ j = i`, such that `f` is a maximal split torus of `H`.

## Proof

The proof is one application of the published reduction
[`simplyConnectedQuasiSplitEnvelope_of_maximalSplitSubgroup`](QuasiSplitEnvelopeReduction.md).
That reduction proves the target from two propositions, and the module supplies a published
proof of each:

- [`maximalSplitSubgroup`](../Rational/MaximalSplitSubgroupProof.md) proves
  [`MaximalSplitSubgroupStatement`](../Rational/MaximalSplitSubgroupStatement.md), the
  existence part of Borel–Tits (1965), Théorème 7.2. It gives a connected reductive closed
  subgroup `F` of `G` through the supplied `S`, with `S` a maximal torus of `F` and with
  roots exactly the nonmultipliable relative roots of `G`. The proof constructs `F` over
  `k` and checks reductivity, maximality and the roots after base change to an algebraic
  closure. It does not use Borel–Tits (1965), 3.22(b).
- [`nonmultipliableCorootSpan`](NonmultipliableCorootSpanProof.md) proves
  [`NonmultipliableCorootSpanStatement`](NonmultipliableCorootSpanStatement.md), the lattice
  consequence of Borel–Tits (1972), Corollaire 4.4 and Remarque 4.5(b), (ii)′. For simply
  connected `G`, it gives full integral coroot span for a root datum on the lattices of
  `S` with their character–cocharacter pairing and those nonmultipliable roots. The
  implementation uses minimal representatives modulo the coroot lattice, not a case split
  by root-system type.

The reduction takes `H = F` and applies the coroot-span result to the root datum of `F`
with respect to `S`. Full coroot span gives semisimplicity and simple connectedness by the
split criteria. The centralizer of this split maximal torus in `F` is the torus itself, so
`F` is quasi-split. Finally, maximal splitness in `G` gives maximal splitness in `F` through
its closed inclusion, and the original factorization `f ≫ j = i` is unchanged.

Both inputs apply at universe `u` to every field, with no condition on the split rank. In
rank zero the subgroup construction still includes `S` (the trivial torus), and there are
no root lines to choose.
