# Sums over the left cosets of an open subgroup

This derived helper module supplies the finite coset sums used to replace Haar
integration in the proof of the unchanged
`CompactCoefficientInjectiveProjectiveStatement` over an arbitrary characteristic-zero
field. All declarations are in `Langlands.Cohomology.SupercuspidalExtCharZero`.

## Provenance

Over a field without a Haar measure, the integral of a compactly supported function
that is right invariant under a compact open subgroup `U` is, up to the volume of `U`,
the finite sum of its values over the left cosets `gU`. Vignéras (1996), Chapter I,
2.4, printed pages 12–13, constructs Haar measures with values in a coefficient ring
in this way: a function constant on the left cosets `gK'` of a compact open subgroup
`K'` is sent to a weighted sum of its values over those cosets. The module is internal
infrastructure. It defines only the counting sum and its elementary laws, without any
normalization, so it involves no measure.

## Declarations

- `cosetSum U f` is the finitary sum `∑ᶠ q : G ⧸ U, f q.out` of `f` over the left
  cosets of a subgroup `U`, evaluated at Mathlib's chosen representatives `q.out`.
  It is defined for every function. When the summand has infinite support,
  Mathlib's `finsum` convention gives the value `0`.
- `RightInvariant U f` states `f (g * u) = f g` for all `g` and all `u ∈ U`.
- `RightInvariant.apply_out`: for a right `U`-invariant `f`, the value at the chosen
  representative of the coset of `g` is `f g`.
- `cosetSum_mul_left`: if `f` is right `U`-invariant, then
  `cosetSum U (fun g => f (a * g)) = cosetSum U f` for every `a`. The proof rewrites
  `f (a * q.out)` as `f (a • q).out` and reindexes the `finsum` along the permutation of
  `G ⧸ U` given by left multiplication by `a`.
- `cosetSum_congr` and `cosetSum_eq_zero` are the pointwise congruence and vanishing laws.
- `finsum_comm_of_finite` exchanges two finitary sums when every nonzero summand
  `F a b` has `a` in a finite set `s` and `b` in a finite set `t`. Both sums are first
  rewritten as finite sums over `s` and `t`, and then `Finset.sum_comm` applies.

## Topological finiteness

For a topological group `G`, the remaining declarations show that finitely many
cosets contribute.

- `finite_image_mk`: if `U` is open, then the image of a compact set `K` in `G ⧸ U` is
  finite, because the quotient is discrete and the image is compact.
- `mem_image_mk_of_out_mem`: if the representative `q.out` lies in `K`, then `q` lies
  in the image of `K`.
- `hasFiniteSupport_out`: if `U` is open and `φ` vanishes off a compact set `K`, then
  `q ↦ φ q.out` has finite support on `G ⧸ U`.
- `hasFiniteSupport_out_of_hasCompactSupport` is the special case where `φ` has
  compact support and `K` is its topological support.
