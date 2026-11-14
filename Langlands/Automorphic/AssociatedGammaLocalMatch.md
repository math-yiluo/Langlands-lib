# From a local pair gamma match to equal family gamma factors

Supporting module of Task 5003 (module
`Langlands.Automorphic.AssociatedGammaLocalMatch`). The stability inputs of the two-twist
engine (`RamifiedGammaStability`, `OutsideGammaStability`) ask that the gamma factors of the
two Hecke families be meromorphically equal at a place. The local theorems (L1, PS, and at the
selected place the target itself) give `IsPairGammaMatch` of the twisted local classes. This
module converts the second into the first. It is an internal deduction from Library results
and the earlier supporting modules of Task 5003.

## Results

- `meromorphicEq_pairDataFactors_gamma`: the gamma factor of twisted pair data
  (`IsTwistedPairData`) is germ-equal at every point to the rational spectral value of every
  certified automorphic gamma factor `G` of `(πη, π')`, where `πη` is any twist of `π`. Proof:
  twist uniqueness and `IsAutomorphicPairGammaFactor.unique` identify `G` with the rational
  gamma expression of the data, and the published
  `rationalSpectralValue_eventuallyEq_polynomialGammaExpression` compares germs.
- `meromorphicEq_arithmeticLocalFactors_gamma`: the gamma factor of arithmetic local factors
  of `(classOf B, classOf B')` with the dual classes is germ-equal to the rational spectral
  value of every arithmetic pair gamma factor `G` of the pair. Proof: the published
  `IsArithmeticPairEpsilonFactor.unique` identifies the epsilon data; `G` is then the rational
  gamma expression of the Euler polynomials of `B ⊗ B'` and its dual (`rationalLRatio_eq`,
  `tensorDualEquiv`); with `eval_inv_algebraMap_total` the gamma factor equals the polynomial
  gamma expression at every `s`.
- `meromorphicEq_gamma_of_isPairGammaMatch`: if the two setups use the same additive character
  at `z`, and `IsPairGammaMatch` holds at `z` for a twist `πη` of the local class of `P` by
  `χ_z`, the local class of `P'`, and the arithmetic classes of `(χ ∘ τ_F) ⊗ S` and `S'`
  along the local map of the arithmetic setup, then the two family gamma factors at `z` are
  meromorphically equal. Both are germ-equal to the rational spectral value of the common `G`
  obtained at the self-dual measure of the automorphic setup; the dual classes are rewritten
  by `localPairClass_dual`.
