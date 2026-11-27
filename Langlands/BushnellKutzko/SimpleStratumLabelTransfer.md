# Strata on chains with the same lattices

`Langlands.BushnellKutzko.Stratum.chainTransfer` moves a stratum
`[𝓛,n,r,b]` to a second lattice chain `𝓛'`, possibly over another
integer ring, whose lattices have the same underlying subsets as those of
`𝓛`. The integers `n`, `r` and the element `b` are kept; the valuation
bound transfers by `LatticeChain.valuation_congr`.

The filtration, valuation, stabilizer and critical exponent of a chain
depend only on the subsets `L_i` (`LatticeChain.mem_endFiltration_congr`,
`valuation_congr`, `mem_stabilizer_congr` and `criticalExponent_congr` in
`RefinementChainTransport`). Hence:

- `isPure_chainTransfer_iff` and `isSimple_chainTransfer_iff`: the moved
  stratum is pure, respectively simple (BK93 (1.5.5), printed p. 43),
  exactly when the original one is;
- `coset_chainTransfer`: the cosets `b + 𝔓^{−r}` agree.

These comparisons identify a stratum over the integral closure
`subfieldIntegers F E` of a subfield `E` with the stratum over the
integers `𝒪[E]` of the spectral local-field structure of `E` on the same
lattices. Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.2 and (1.5.5), printed pp. 24–25 and 43.
