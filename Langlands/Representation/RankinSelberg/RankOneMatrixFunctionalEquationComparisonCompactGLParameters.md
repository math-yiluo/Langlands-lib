# Joint compact parameters in the natural GL₁ orbit comparison

This internal derived module retains the compact parameter outside the actual
unipotent orbit integral. For a continuous translate map `U`, a
Schwartz–Bruhat parameter kernel `κ`, and an ambient matrix test `Φ`, the two
integrands are

```text
κ(x) |det g| ∫_N χ(u)⁻¹ Fourier(Φ)(iota(u) W⁻¹ diag(g,1,...) U(x)) du,
κ(x) |det g| ∫_N χ(u)⁻¹ Φ(u block(g,Z) B iota(U(x))) du.
```

Here `W` and `B` are the actual signed Weyl and complementary block Weyl
representatives. The full product measures are `μ × GL₁Haar` and
`μ × GL₁Haar × rectangularMeasure ν m 1`, respectively. The theorem
`signedWeylGL_blockGL_parameter_duality` proves genuine integrability on
both full products and equality of their integrals. The same `μ`, `κ`,
`U`, `Φ`, character, and self-dual additive measure occur on both sides.
It requires determinant norm one for `U(x)` wherever `κ(x)` is nonzero.

The parameter family of matrix translates is uniformly locally constant as
a family of functions. Applying the unipotent integral and the scalar
weight preserves this property. Multiplication by `κ` gives compact support
in the parameter. The finite sampled-value Schwartz expansion from
CompactOrbitIntegration then turns section convergence into joint
convergence. Each section uses WeylOrbitBlocks and ScalarHaar. Only after
joint convergence is proved does Fubini integrate the section identities.
The additive-to-GL₁ scalar is identical on both sides and cancels.

This strengthens the compact-average formulation by proving convergence
before averaging in the compact parameter; cancellation inside that
average is not used to infer a bound. It covers every canonical p-adic field
in an arbitrary universe, every bundled nontrivial additive character and
supplied self-dual Haar measure, and every `m ≥ 0`. It proves no model
realization, spectral continuation, or gamma comparison. Its provenance is
the source-free combination of the cited internal orbit, finite-family,
matrix-translate and scalar-Haar results.
