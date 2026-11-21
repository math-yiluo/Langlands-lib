# Weighted L² estimates for one-sided translation recurrences

`Langlands.Analysis.L2SlabRecurrenceStatement`, proved by `l2SlabRecurrence`,
is the one-height estimate and square-integrability statement for a supplied
renormalizing shift on a measure space. The shift `σ` is measurable, increases
a measurable real height `h` by one, and pushes the measure `μ` forward to
`c² μ` with `c > 0`. The slab `(a,b]` means the preimage under `h`. The norm
notation below is the `lpNorm` for the measure restricted to the indicated
region. The function `f` is strongly measurable and can take values in a
complex normed space.

For degree `m` and lower coefficients `pₖ`, define the residual
`D f = f ∘ σᵐ + ∑ₖ₌₀ᵐ⁻¹ pₖ (f ∘ σᵏ)`. Put
`q = ∑ₖ₌₀ᵐ⁻¹ |pₖ| cᵏ` and assume `q < cᵐ`. If `f` is square-integrable on
`(0,m]` and `D f` is square-integrable on `h > 0`, then `f` is
square-integrable on `h > 0`, and

```
‖f‖_{h>0} ≤ (cᵐ ‖f‖_{(0,m]} + ‖D f‖_{h>0}) / (cᵐ − q).
```

The `MemLp` conclusion is explicit: the inequality is not justified by
assigning a zero real-valued `lpNorm` to a non-square-integrable function.
In particular, zero residual and square-integrable initial data suffice.

## Implemented proof

- `L2RenormalizingShift.map_iterate` iterates the measure identity. Restrict
  the pushforward to a measurable set and take its preimage to move the
  pullback norm to the original function. In exponent two, the measure
  scaling `(cᵏ)²` becomes the norm scaling `cᵏ`
  (`eLpNorm_iterate_preimage`). The height identity identifies the preimage
  of a translated slab with the original slab (`eLpNorm_iterate_slab`).
  The scale is finite and nonzero, so membership is equivalent on these
  two sides (`memLp_iterate_slab_iff`).
- First prove square-integrability on each `(0,m+N]`, by induction on `N`.
  For the step, the lower translates on `(0,N+1]` use only heights at most
  `m+N`. On that slab the top translate equals the residual minus the
  finite lower sum; it is therefore square-integrable. Transporting it
  back gives membership on `(m,m+N+1]`. Combine with the initial slab.
- Let `M_N = ‖f‖_{(0,m+N]}`. For the residual identity on `(0,N]`, the
  lower translates have total norm at most `q M_N`, while the top
  translate has norm `cᵐ ‖f‖_{(m,m+N]}`. The triangle inequality on the
  disjoint slabs bounds `M_N` by the sum of their norms. Combining gives
  `(cᵐ−q) M_N ≤ cᵐ ‖f‖_{(0,m]} + ‖D f‖_{h>0}`.
- Convert these finite truncated norms to bounds for the extended norms.
  Monotone convergence for the indicators of `‖f‖ₑ²` on the increasing
  slabs gives the extended-norm bound on their union `h > 0`. Its finiteness
  proves `MemLp`, and applying `ENNReal.toReal` gives the asserted real
  inequality.

## Provenance and scope

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §7.5, pp.217–218
(the one-dimensional lemma), and §7.6, pp.219–220 (the membership step).
This is a derived variant, not the lemma with its full root hypothesis.
The stronger coefficient condition is sufficient for the intended weighted
application, where `c` is made large relative to the coefficients. The
source derives its estimate on `L²` by factoring the polynomial; here
one instead isolates the leading translate and uses truncated slabs so
that the same estimate establishes membership. This module does not yet
combine the directions or construct the adelic shift and measures.
