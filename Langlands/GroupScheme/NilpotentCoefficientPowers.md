# Powers in nilpotent coefficient kernels

Worker 801 supplies an internal extension of the published square-zero kernel
power theorem to arbitrary nilpotent ideals. The actual affine group scheme is
over an arbitrary ring in universe `u`; it need not be smooth or commutative.

For an ideal `I` of a test algebra `A`, the transition from `A/I^(n+2)` to
`A/I^(n+1)` has square-zero kernel. Every natural number whose image in `A`
belongs to `I` annihilates this kernel. The published
`Lie.affineKernel_pow_eq_one` therefore moves powers of a point through the
successive reductions. If `x` reduces to the identity modulo `I`, then
`x^(p^n)` reduces to the identity modulo `I^(n+1)`. When that ideal vanishes,
affine coordinates give `x^(p^n) = 1` in the original group of points.

This is an internal derived argument, following the adjacent-quotient calculation
of `IntegralModel.CongruencePowers` without its integral-model hypotheses. It is
the positive-residue-characteristic part of the Artinian argument of SGA 3,
Exposé IX, Lemma 6.1, registered source `sga3-expose-ix-gille-polo-2009`,
recomposed page 53 (PDF page 23). It asserts no existence of a field exponent
or global exponent by itself.
