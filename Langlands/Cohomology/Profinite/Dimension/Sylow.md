# Cohomological dimension of pro-`p` groups

`Langlands/Cohomology/Profinite/Dimension/Sylow.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a pro-`p` group the only simple smooth module killed by `p` is `ℤ/p` with trivial action;
hence `cd p G ≤ n` iff `H^{n+1}(G, ℤ/p) = 0`.

## Declarations

- `exists_bijective_hom_of_isProPGroup`: for a profinite pro-`p` group `G` and a simple smooth
  module `A` killed by `p`, there is a bijective morphism from the trivial module `ℤ/p` to `A`.
- `cd_le_iff_of_isProPGroup`: for a profinite pro-`p` group, `cd p G ≤ n` iff
  `H^{n+1}(G, ℤ/p) = 0` (trivial coefficients `ULift (ZMod p)`).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/CohomologicalDimension/NotDvdSuperIndexBotOfIsProPGroup.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's, with
`cdp_le_iff_of_isProPGroup` → `cd_le_iff_of_isProPGroup`.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §4.1, Propositions 20 and 21, p. 27 (a simple discrete module
  killed by `p` over a pro-`p`-group is `ℤ/pℤ`; `cd(G) ≤ n` iff `H^{n+1}(G, ℤ/pℤ) = 0`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §3, Proposition (3.3.2), p. 172 (for a pro-`p`-group,
  `cd G ≤ n ⇔ H^{n+1}(G, ℤ/pℤ) = 0`); simple modules: chapter I, §6, Corollary (1.6.13), p. 71.
