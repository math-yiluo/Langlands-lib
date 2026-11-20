# Simple approximation of a pure stratum

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (2.4.1)(i),
first two sentences, printed p. 65 (PDF p. 77). The proof is on printed
pp. 66–75.

`PureStratumSimpleApproximationStatement` is an unproved proposition
definition. It quantifies over every nonarchimedean local field `F` and
finite-dimensional `F`-vector space `V`, in independent universes.

For every pure stratum `S = [𝔄,n,r,β]`, it asserts that there is a stratum
`T` with

- the same lattice chain as `S`, and the same integers `n` and `r`;
- `T` simple (`Stratum.IsSimple`);
- `S` equivalent to `T` (`Stratum.Equivalent`, equality of cosets
  `β + 𝔓^{−r}`);
- `e(F[T.b]|F)` dividing `e(F[S.b]|F)`, and `f(F[T.b]|F)` dividing
  `f(F[S.b]|F)`.

The invariants are the published `elementRamificationIndex F` and
`elementResidueDegree F` of the actual generated algebras. Both
algebras are fields here, because `S` is pure and `T` is simple, so the
nonfield default value zero of these definitions is not used.

## Relation to the source

The source's first sentence of (2.4.1)(i) is the existence of the simple
equivalent `T`. Its second sentence asserts divisibility for *every*
simple `T` equivalent to `S` with the same order and integers. This
statement asks for divisibility only for the stratum it produces. That is
a weaker, derived form of the source sentence. Together with (2.4.1)(ii)(b),
stated in the Library as `StratumEquivalenceStatement` (T5), it gives the
source's universal form: any two such simple strata have the same
invariants. That derivation is carried out in the T7 reduction, not here.

The source's common hereditary order is represented by one fixed
lattice-chain presentation, via the equation `T.chain = S.chain`.
