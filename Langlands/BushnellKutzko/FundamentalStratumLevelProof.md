# A contained fundamental stratum computes the normalized level

`Langlands.BushnellKutzko.FundamentalStratumLevelProof` proves the published
proposition `Langlands.BushnellKutzko.FundamentalStratumLevelStatement`.

```lean
theorem Langlands.BushnellKutzko.fundamentalStratumLevel :
    Langlands.BushnellKutzko.FundamentalStratumLevelStatement.{uK, uV}
```

The proposition ranges over a prime `p`, a p-adic field `K`, a rank `n ≥ 1`,
a level-one additive character `ψ`, an irreducible admissible class `a` of
`GL_n(K)`, a lattice chain `𝓛` in `K^n`, an index `m ≥ 1` and an endomorphism
`b ∈ 𝔓^{-m}(𝓛)`. If `a` contains the stratum and every representative of
`b + 𝔓^{1-m}(𝓛)` is non-nilpotent, then `m / 𝓛.period` is an attained and
minimal normalized level value. The field and representation carrier have
independent universes `uK` and `uV`.

Bushnell–Kutzko (1993), Introduction, printed p. 8, states the common normalized
level of contained fundamental strata. Its §2.3, printed p. 57, gives the
nilpotent-coset definition and the smaller-level criterion
(`bushnell-kutzko-1993-admissible-dual-gln`). See also Bushnell (1987), Theorem 1,
printed p. 192, Remark (2.9), printed p. 195, and (3.3) and Theorem 2′,
printed pp. 196–197 (`bushnell-1987-hereditary-orders-gauss-sums`). The operator
note's Lemma 4.11(i), printed pp. 15–16, gives the intertwining argument
for the normalized-level equality (`operator-numerical-llc-route-2026-11-16`).

## Proof

The entry module imports `FundamentalStratumLevelStatement` and
`FundamentalStratumLevelCore`. After introducing the binders of the published
proposition, it applies `fundamentalStratumLevel_of_containsStratum` to the
same arguments. The canonical instance definitions in the two imports agree
by definitional unfolding. The core theorem obtains attainment by triviality
on `U^{m+1}` and proves minimality by constructing a nilpotent representative
from a hypothetical smaller attained value. The details are in
`FundamentalStratumLevelCore.md`.

Worker 408 authored the original Lean proof. This contribution uses the shared
lattice-chain basis and filtration coordinate lemmas and the published cyclic
subrepresentation construction.
