# Adelic gauges in simple-root coordinates

This module defines an internal analytic interface for global Whittaker
estimates. It follows Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms
on GL(3) II* (1979), §12.1, printed pages 226–227, source
`jps-1979-gl3-ii`. The local antecedent is §2.3 of *Automorphic forms on GL(3) I*,
printed pages 183–184, source `jps-1979-gl3-i`. The definition in §12.1 is given
for every rank, although the article's main application has rank three.

All declarations retain an arbitrary number-field universe `u`. For
`GL_(r+1)`, a diagonal is a tuple `d` of `r+1` actual ideles. Its simple
roots are `d_i / d_(i+1)`, for `0 ≤ i < r`. In the source's coordinates
`d_i = a_i ⋯ a_r`, these ratios are exactly `a_0, …, a_(r-1)`; the final
coordinate `a_r` is a scalar factor.

The supporting definitions are concrete:

- `gaugeDiagonalPoint F n d` transports the matrix `diag(d)` through
  `GeneralLinearGroupPoints.adelicEquiv` to the actual carrier `Points F n`.
- `gaugeStandardCompact F n` pulls back
  `PrimitiveAdelicHeight.standardCompact F n` through that same equivalence.
- `gaugeSimpleRootIdeles F r d` is the tuple of adjacent diagonal ratios.
- `gaugeSimpleRootRow F r d` views those ratios in
  `RowVector F r = Matrix (Fin 1) (Fin r) (Adeles F)`.
- `gaugeSimpleRootNormProduct F r d` is the product of their normalized
  absolute values `IdeleAbsoluteValue.full F`, coerced to real numbers.

The test function lies in the published `schwartzBruhat F r`, the complex
span of products of archimedean Schwartz functions and locally constant,
compactly supported finite-adelic functions.

`IsAdelicSimpleRootGauge F r τ Ξ` says that `τ ≥ 0`, that `Ξ` is measurable,
that it is invariant under left multiplication by the full adelic upper
unipotent and under right multiplication by the standard compact subgroup,
and that its diagonal restriction is

`Ξ(diag d) = |∏_(i<r) (d_i / d_(i+1))|^(-τ) · ‖Φ((d_i / d_(i+1))_(i<r))‖`.

Here the absolute value of a product means the product of the normalized
idelic absolute values. The exponent `τ` is a parameter of the predicate;
uniform choices of it are requested separately in the analytic statements.

There are three explicit changes from Part II §12.1. The predicate includes
measurability, allows `τ = 0` where that source takes `τ > 0`, and uses
`‖Φ‖` for a complex Schwartz–Bruhat function in place of a nonnegative
Schwartz–Bruhat function. The norm need not itself be smooth, and no
equivalence with the source's class of gauges is asserted. The codomain is
the extended nonnegative reals so that the same object can occur directly
in lower integrals. The displayed diagonal formula has finite values,
since each simple root is an idele with strictly positive finite norm.

This is a definition only. In particular, the module asserts neither the
existence of a gauge majorizing a Whittaker function nor the convergence of
any gauge integral. Those require separate analytic results. The diagonal
formula is unchanged by multiplying every `d_i` by the same idele. Together
with Iwasawa decomposition and the two invariances, this implies central
invariance mathematically; this module does not prove that consequence.

A determinant twist, when needed for a nonunitary central character, is kept
outside the gauge. Part I, Proposition (2.3.6), writes the modulus of the
central character as `|·|^c` for `GL_m` and bounds the Whittaker function
twisted by `|det|^(-c/m)` by a gauge. Thus the corresponding untwisted
estimate has the factor `|det|^(c/m)` outside the gauge. The shared
majorization statement uses a specified common exponent `β` there.
