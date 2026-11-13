# `L²(G, χ, dg*)₀` is the space of smooth vectors of its Hilbert completion

Author: Worker 28.

`Langlands.Renard.CompactRepresentation.centralL2SmoothVectors` proves
`CentralL2SmoothVectorsStatement` (Renard 2026, IV.3.1, Remark, printed p.99 /
PDF p.105) in universe `uG`, with no added hypothesis. Below,
`b = centralL2Form χ hχ μ`, `ρ = centralL2Representation χ hχ μ`, and
`toHilbert : L²(G, χ, dg*)₀ → b.HilbertCompletion` is the canonical linear map.
The helper lemmas are in the namespace `CentralL2SmoothVectorsProof`.

## Images are smooth (⇐)

Let `f ∈ L²(G, χ, dg*)₀`. The published `centralL2Representation_smooth` gives
an open subgroup `K` that fixes `f`. The completed action agrees with `ρ` on
`toHilbert` images (`completedRepresentation_toHilbert`), so `K` also fixes
`toHilbert f`.

## Smooth vectors are images (⇒)

Let an open subgroup `U` fix `w`. `G` is locally compact, Hausdorff and totally
disconnected, so `Topology.isLocallyProfinite_of_mathlib` and van Dantzig's
theorem (`Topology.LocallyProfiniteProof.vanDantzig`) give a compact open
subgroup `K ≤ U`. Then `K` fixes `w`. The rest of the argument has two steps.
First, `w` is a limit of `toHilbert` images of right `K`-invariant elements.
Second, such limits are again `toHilbert` images.

### Approximation by `K`-invariant elements (`exists_fixed_near`)

Let `v ∈ L²(G, χ, dg*)₀`. By smoothness an open subgroup `L` fixes `v`. Set
`L' = L ∩ K`, written in Lean as `L.subgroupOf K`. `L'` is open in the compact
group `K`, so `K / L'` is finite (`Subgroup.quotient_finite_of_isOpen`). For a
coset `c` define `φ c = ρ(c.out) v`. Because `L'` fixes `v`, this gives
`φ (kL') = ρ(k) v` for every `k ∈ K`. It follows that
`ρ(k) (φ c) = φ (k • c)`. The average

`f = |K / L'|⁻¹ • ∑_c φ c`

is therefore fixed by `K`, since left translation by `k` permutes the cosets
(`Equiv.sum_comp`). The completed action is isometric
(`completedRepresentation_norm`) and fixes `w`. Hence each term satisfies
`‖toHilbert (φ c) − w‖ = ‖ρ̂(k)(toHilbert v − w)‖ = ‖toHilbert v − w‖`, where
`ρ̂` is the completed action and `c = kL'`.

The generic lemma `norm_avg_sub_le` concerns any complex normed space: an
average of finitely many vectors, each at distance `r` from `w`, lies within
distance `r` of `w`. It gives `‖toHilbert f − w‖ ≤ ‖toHilbert v − w‖`. The
range of `toHilbert` is dense (`denseRange_toHilbert`), so `w` is in the
closure of the set of `toHilbert` images of `K`-fixed elements. Since the
completion is a metric space, a sequence `toHilbert (f n) → w` with every
`f n` fixed by `K` exists.

### Closedness (`exists_toHilbert_eq_of_tendsto`)

Let `sqIntegral F = ∫⁻ ofReal (centralNorm F q ^ 2) dμ(q)` for a
centrally covariant smooth function `F`. For elements of `L²(G, χ, dg*)₀` this
quantity equals `ofReal ‖toHilbert f‖²` (`ofReal_norm_toHilbert_sq`). This
uses `norm_toHilbert`, `centralL2Form_inner_self`, the integrability of the
squared descended norm and `ofReal_integral_eq_lintegral_ofReal`.
Conversely, when `sqIntegral F < ∞` the function `F` lies in the published
square-integrable subspace (`mem_centralL2Submodule_of_sqIntegral_lt_top`, via
`memLp_two_iff_integrable_sq`).

For `x ∈ G`, let `cosetImage K x` be the image of `xK` in `G / Z(G)`. It is
open and compact, so its measure `m_x` is positive and finite (Haar measure).
If `F` is right `K`-invariant, then `centralNorm F` is constant, equal to
`‖F x‖`, on that image. Comparing with the indicator function gives
`ofReal(‖F x‖²) · m_x ≤ sqIntegral F` (`ofReal_mul_measure_le_sqIntegral`),
hence `‖f(x)‖² · m_x ≤ ‖toHilbert f‖²` for `K`-fixed `f`
(`norm_eval_sq_mul_le`).

Apply this bound to `f p − f q`, which is `K`-fixed. Since `toHilbert (f n)`
is Cauchy, the sequence `f n (x)` is Cauchy in `ℂ` for each `x`. Its limit
`F₀ x` (`limUnder`) is `χ`-covariant and right `K`-invariant, both properties
passing to the limit by uniqueness of limits. The published `smoothFunctionOf`
therefore makes it a smooth covariant function `F`.

Fix `n`. Pointwise on `G / Z(G)`, the function `ofReal(centralNorm(f n − f p)²)`
tends to `ofReal(centralNorm(f n − F)²)` as `p → ∞`. Its integrals,
`ofReal ‖toHilbert (f n) − toHilbert (f p)‖²`, tend to
`ofReal ‖toHilbert (f n) − w‖²`. Fatou's lemma (`lintegral_liminf_le'`, with
measurability from local constancy) gives

`sqIntegral (f n − F) ≤ ofReal ‖toHilbert (f n) − w‖² < ∞`.

So `f 0 − F` is square integrable, and hence so is
`F = f 0 − (f 0 − F)`. The bound then reads
`‖toHilbert (f n) − toHilbert F‖ ≤ ‖toHilbert (f n) − w‖ → 0`. Squeezing gives
`toHilbert (f n) → toHilbert F`, and uniqueness of limits gives
`toHilbert F = w`.

## Scope

The proof is internal and elementary. It does not construct the averaging
projector `e_K = ∫_K π(k) dk` that Renard's route suggests. Instead it uses a
finite average over `K / (L ∩ K)`, chosen for the vector being approximated.
It also does not identify the `K`-invariant subspace with a weighted `ℓ²`
space; it uses a direct pointwise Cauchy and Fatou argument. It uses only
published Library results on `L²(G, χ, dg*)₀`, its Hilbert completion and
locally profinite groups, together with Mathlib.
