# The global Whittaker coefficient of a cusp form

Author: Worker 1709.

This is internal infrastructure for the proof of
`Langlands.Automorphic.CuspidalUnitaryLocalGenericityStatement`. It iterates the column
coefficients of `Columns`. Starting from a continuous, rational-left-invariant, cuspidal
function `φ` on `GL_{r+1}(𝔸_K)`, it produces a function `W_φ = descend r φ` given by iterated
column integrals. Classically, `W_φ` is the global Whittaker coefficient
`∫_{N(K)\N(𝔸_K)} φ(u g) conj(ψ(Σᵢ u_{i,i+1})) du`. This module does not prove that identity
and does not need it. It proves only the properties below. All results are proved, with no
hypothesis beyond `CompactSpace (AdeleQuotient K)`.

## Iteration

- `LevelProps c F` bundles the four level-`c` properties of `Columns`: continuity,
  `MirInvariant c`, `BlockVanishing c` and `Equivariant c`. `LevelProps.colCoeff` says that
  for `c < r`, `LevelProps (c + 1) F` implies `LevelProps c (colCoeff c F)`. Each component is
  one of the four steps.
- `descend k F` applies the column coefficients for the columns `k, k − 1, …, 1`:
  `descend 0 F = F` and `descend (k + 1) F = descend k (colCoeff k F)`.
- `levelProps_descend`: for `k ≤ r`, `LevelProps k F` implies `LevelProps 0 (descend k F)`. At
  level `0`, `Equivariant 0` is the Whittaker transformation law
  `W(u g) = ψ(Σᵢ u_{i,i+1}) W(g)` for every upper unitriangular adelic `u`.
- `exists_descend_ne_zero`: under `LevelProps k F`, if `F` is not identically zero then neither
  is `descend k F`. This is the nonvanishing step applied at every level.
- `descend_add`, `descend_const_mul` and `descend_mul_right` make `descend` additive,
  homogeneous, and compatible with right translation.

## The starting level

`blkUnit_eq_blockUnipotent` identifies the block element `blkUnit m r X` with the Library's
`blockUnipotent hab (blockPart hab X)` for the `(m, r + 1 − m)` block parabolic.
`blockPartHom`, the projection of torus coordinates to the `m × (r + 1 − m)` block, is a
continuous surjective additive map. `integral_comp_surjective` then gives
`torusIntegral_blkUnit_eq_constantTerm`: the torus block integral of
`evaluate K (r + 1) f (blkUnit m r X · g)` equals the Library's
`constantTerm K (r + 1) hab f g`, normalized by `matrixQuotientHaar`.

`levelProps_top`: let `f : ContinuousRationalFunctions K (r + 1)` have vanishing constant terms
along every standard maximal block parabolic. Then `LevelProps r (evaluate K (r + 1) f)`, as
follows.

- Continuity and rational left invariance are the Library's `continuous_evaluate` and
  `evaluate_rational`.
- Block vanishing at level `r` is the vanishing of the constant terms with `1 ≤ m ≤ r`.
- At level `r`, `IsUpperColId r u` forces `u = 1` and `superSum r u = 0`, so equivariance is
  trivial.
