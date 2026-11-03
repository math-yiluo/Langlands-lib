# Homogeneous coordinates of rational points and closed sets of projective space

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. It describes
points of `ProjectiveSpace K n = Proj K[X_0, …, X_n]` over a field `K` by
homogeneous coordinates in `K^(n+1)`. It also shows that a closed set contains
every point whose coordinates satisfy all homogeneous equations that hold on a
given set of coordinate vectors of points of the closed set.

## Definition

- `HasCoordinates x c`: the point `x` has homogeneous coordinates
  `c : Fin (n + 1) → K`. This means that for every `d` and every polynomial `h`
  that is homogeneous of degree `d`, `h` lies in the homogeneous prime of `x`
  exactly when `h(c) = 0`.

The definition only tests homogeneous polynomials. Membership of an arbitrary
polynomial in the prime of `x` is then decided by its homogeneous components, by
`mem_asHomogeneousIdeal_iff_homogeneousComponent` below.

## Results

- `decompose_coe_eq_homogeneousComponent`: the graded decomposition of the
  coordinate ring takes `h` to its homogeneous components.
- `mem_asHomogeneousIdeal_iff_homogeneousComponent`: `h` is in the prime of `x`
  exactly when all of its homogeneous components are.
- `HasCoordinates.smul`: coordinates can be rescaled by any nonzero scalar.
- `HasCoordinates.ne_zero`: coordinates are nonzero. If `0` were a coordinate
  vector, every homogeneous polynomial of positive degree would lie in the prime,
  so the prime would contain the irrelevant ideal.
- `HasCoordinates.linearAction`: if `x` has coordinates `c` and `e` is a linear
  automorphism of `K^(n+1)`, then `ProjectiveSpace.linearAction K n e x` has
  coordinates `e c`. The proof uses `linearAction_mem_iff`, and the fact that
  linear substitution preserves homogeneity and turns evaluation at `c` into
  evaluation at `e c`.
- `mem_asHomogeneousIdeal_iff_not_mem_basicOpen`: `h` is in the prime of `x`
  exactly when `x` is not in the basic open `D₊(h)`.
- `irrelevant_map_eval_eq_top`: for `c ≠ 0` and a ring map
  `ψ : K → Γ(Spec K, ⊤)`, the irrelevant ideal maps onto the unit ideal under
  `ψ ∘ eval c`, because a coordinate `X_i` with `c i ≠ 0` goes to a unit.
- `hasCoordinates_fromOfGlobalSections`: the rational point
  `Spec K → ProjectiveSpace K n` given by `Proj.fromOfGlobalSections` for the map
  `ψ ∘ eval c` has coordinates `c` at the closed point. For degree `0`, `h` is a
  constant, and a nonzero constant is a unit, which cannot lie in a prime. For
  positive degree, `Proj.fromOfGlobalSections_preimage_basicOpen` pulls `D₊(h)`
  back to the basic open of `ψ(h(c))` in `Spec K`. That open is everything when
  `h(c) ≠ 0` and empty when `h(c) = 0`.
- `HasCoordinates.exists_eq_smul`: any two coordinate vectors of one point are
  proportional by a nonzero scalar. Choose `i` with `c i ≠ 0`. The linear form
  `c i X_l - c l X_i` vanishes at `c`, so it lies in the prime, so it vanishes at
  `c'`. This gives `c' = (c' i / c i) • c`.
- `mem_of_isClosed` (closed sets on rational points): let `Z` be closed and `S` a
  set of vectors, each of which is a coordinate vector of some point of `Z`.
  Suppose every homogeneous `f` that vanishes on `S` also vanishes at `c`. Then
  every point `y` with coordinates `c` lies in `Z`. Since `Z` is closed, it is the
  zero locus of its vanishing ideal
  (`ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure`). Each homogeneous
  component of an element of that ideal lies in the primes of the points of `Z`,
  so it vanishes on `S`, so it vanishes at `c`, so it lies in the prime of `y`.

## Provenance

These are internal helper definitions and lemmas. They give the standard
description of rational points of projective space by homogeneous coordinates
and of closed sets by homogeneous equations. They are used in the closed-orbit
step of the proof of Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 17.65 (printed pp. 374-375). There, the
points of the orbit `G · [v]` are the lines `[ρ(g) v]`, the orbit is closed
because `G/B` is complete, and a limit of points of the orbit stays in it. The
limit itself is computed on coordinates in `Langlands.GroupScheme.FlagCoreLimit`.
