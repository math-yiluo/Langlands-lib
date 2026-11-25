# Locally constant cochains and the cohomology of a topological group

`Langlands/Cohomology/Profinite/Cochains.lean`, namespace `Langlands.ProfiniteCohomology`.

For a topological group `G` (in practice profinite), a commutative ring `k` and a smooth
representation `A : Rep k G` (`IsSmoothRep A`), the cohomology `Hⁿ(G, A)` is computed by the
complex of locally constant inhomogeneous cochains. This is the definition of Serre (continuous
cochains with values in a discrete module are exactly the locally constant ones) and of
Neukirch–Schmidt–Wingberg. It is the cochain model on which the Library's Galois cohomology is
built; it is compared with Mathlib's `groupCohomology` (discrete groups,
`Comparison/Discrete.lean`), with Mathlib's `continuousCohomology` and with the Library's
`Langlands.Continuous.finiteQuotientCohomology` (the modules of `Comparison/`).

## Declarations

- `locallyConstantCochains A n`: the submodule of the locally constant maps `G^n → A` in the
  module of all maps; `mem_locallyConstantCochains` unfolds membership.
- `continuous_contractNth`: the face maps `G^{n+1} → G^n` (multiplying two adjacent entries) are
  continuous.
- `isLocallyConstant_d`, `d_mem_locallyConstantCochains`: the inhomogeneous differential of
  Mathlib's complex sends locally constant cochains to locally constant cochains (for smooth
  `A`).
- `dLocallyConstant A n`: the restricted differential, with `dLocallyConstant_hom_apply` (it is
  Mathlib's differential) and `dLocallyConstant_comp` (`d ∘ d = 0`).
- `cochains A`: the cochain complex of locally constant cochains, with `cochains_X`, `cochains_d`.
- `cochainsι A`: its inclusion into Mathlib's `groupCohomology.inhomogeneousCochains A`, a
  monomorphism in each degree.
- `cocycles A n`, `cohomology A n`, `cohomologyπ A n`: the cocycles, the cohomology module
  `Hⁿ(G, A)` (an object of `ModuleCat k`) and the projection from cocycles to cohomology.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Source names:
`cochainsComplex` → `cochains`, `cochainsComplexι` → `cochainsι`, `cochainsComplex_X`,
`cochainsComplex_d` → `cochains_X`, `cochains_d`; the others keep their names. The coefficient
class `IsDiscreteRep` is replaced by `IsSmoothRep` (`SmoothCoefficients.lean`); proofs are
unchanged.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.2, p. 10 (continuous cochains; with discrete coefficients,
  “continuous” amounts to “locally constant”).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §2, pp. 12–14 (standard resolution (1.2.1), p. 12;
  homogeneous cochains and Definition (1.2.2), p. 13; inhomogeneous cochains, p. 14).
  Neukirch–Schmidt–Wingberg define `Hⁿ(G, A)` by homogeneous cochains and show on p. 14 that the
  inhomogeneous ones compute it.
