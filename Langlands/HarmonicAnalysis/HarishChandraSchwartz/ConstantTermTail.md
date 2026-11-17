# Rapid unipotent tails from the full constant-term estimate

This internal analytic consequence of the Library's full
`ConstantTermEstimate` supplies the tail step needed in the VIII.3.1
cuspidal cancellation argument. The full constant-term estimate and the
height-product bound remain explicit analytic inputs.

`ConstantTermTailEstimate` says that for every real Levi decay exponent
`d` and nonnegative real tail exponent `p`, there are an ambient exponent
`d'` and a nonnegative finite constant `c` with the following property.
For any subset `V` of the unipotent subgroup and any positive `t` such
that `t ≤ 1 + σ(u)` on `V`,

```text
sqrt(δ(m)) ∫_V Ξ(m u) (1 + σ(m u))^(-d') du
  ≤ c t^(-p) ΞM(m) (1 + σM(m))^(-d).
```

The displayed integrals mean the nonnegative lower integrals of the
`ENNReal.ofReal` kernels in Lean. No measurability or compact-conjugation
invariance of `V` is required.

`ConstantTermEstimate.tail` proves this proposition assuming nonnegative
`Ξ` and `σ` and `SigmaProductBound M U σ`, in addition to the full
constant-term estimate on every `m`. Take the ambient exponent from that
estimate at `d`, and add `p`. If `C > 0` is the height-product constant,
then on the tail

```text
C t ≤ C (1 + max(σ(m), σ(u))) ≤ 1 + σ(m u).
```

Raising this inequality to the nonpositive power `-p` extracts
`C^(-p) t^(-p)` from the weighted kernel. Enlarge the restricted lower
integral to the whole unipotent group, and apply the original
constant-term estimate. The new constant is its constant multiplied by
`C^(-p)`.

This argument uses the already global constant-term estimate, so it
needs no new compact double-coset extension and does not require exact
compact invariance of `Ξ` or the matrix height. It asserts no actual-point
II.4.5 theorem and does not discharge the actual analytic prerequisites.
