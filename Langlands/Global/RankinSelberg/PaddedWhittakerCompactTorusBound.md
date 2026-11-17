# Compact-uniform padded Whittaker torus integrals

The internal definition `paddedWhittakerTorusKernel` is the extended norm of
an arbitrary coefficient `W` at `pad(diag(d) * c)`, multiplied by the smaller
group's determinant norm to the real power `σ` and by fixed real powers `κ j`
of the full idele norms of the block roots. Here `d` is a tuple of actual
ideles and `c` is an actual point of the smaller adelic general linear group.
This definition uses no quotient representative or Haar normalization.

The supporting theorem `exists_padded_whittaker_compact_torus_bound` proves
a uniform finite bound for the integral of this kernel when `W` is a
Whittaker function, as `c` varies in any compact subset of the smaller group.
It assumes a Whittaker decay class and a common determinant-power bound with
exponent `β`. For prescribed real block-root weights `κ`, the sufficient
condition is `β + σ > 3 + ∑ j, |κ j|`. The threshold is independent of the
compact set, vector, and standard additive character. The conclusion is
written with the kernel expanded and permits every torus Haar measure.

The proof applies the compact-uniform diagonal Schwartz theorem to the image
of the compact set under padding. Its one symmetric Schwartz–Bruhat function
therefore bounds every right translate in the compact set. The actual-point
gauge construction provides an exponent-zero gauge with this same diagonal
profile. The padded torus Mellin theorem shows that its integral, with
determinant exponent `β + σ` and weights `κ`, is finite.

The remaining dependence on the right translate is its determinant norm
raised to `β + σ`. This continuous real function is bounded above on the
compact set, also when that set is empty. Multiplicativity of the determinant
norm and positivity of its real powers separate that factor from the torus
integrand. Conversion to extended nonnegative reals, monotonicity of the lower
integral, and extraction of the finite constant give the uniform bound.

The result is derived from the named imported construction and Mellin modules.
It integrates actual torus points with any Haar normalization. It does not
identify this integral with a Whittaker-quotient integral or assert a formula
for its conjugation modulus; those are separate inputs.
