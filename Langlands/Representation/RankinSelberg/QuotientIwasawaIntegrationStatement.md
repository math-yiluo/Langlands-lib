# Normalized quotient Iwasawa integration

`Langlands.RankinSelberg.QuotientIwasawaIntegrationStatement` states the
Iwasawa measure identity on the actual left quotient
`N_(n+1) \ GL_(n+1)(F)`. This module supplies one proposition definition;
it supplies no proof of that proposition.

The parameters are every prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and natural `n`, so the actual rank is `n+1`.
The statement installs the topology, valuation and nonarchimedean local-field
structure from `T`, as in `AnalyticStatement`. It uses Borel measurable
structures on the field units, general linear group, actual upper-unipotent
subgroup, and quotient, and the usual finite-product measurable structures
on diagonal coordinates and their product with the group. It retains the
unipotent right-invariance instance needed by `QuotientIntegration.IsCompatible`.
Every compatible quotient measure is quantified; no integration identity is
assumed beyond that existing predicate's compact-test Weil formula.

Write `m = n+1`, `A = (Fˣ)^m`, and
`K = Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n`.
The local bindings in the proposition have the following mathematical meanings:

- `da` is the finite product of `localMultiplicativeHaar F.Carrier` on `A`.
- `dk` is `generalLinearHaar F.Carrier n` restricted to `K`, regarded as a
  measure on the ambient group. Thus the product is on `A × GL_m(F)` with its
  second coordinate supported on `K`; no subtype transport is implicit.
- `δ(a) = ∏_{i<j} T.normalizedAbs(a_i/a_j)` uses ordinary diagonal entries.
- `q(a,k)` is the class of `Iwasawa.diagonalUnits a * k` in the left quotient,
  using the published `QuotientIntegration.leftQuotientMap`.

The exact conclusion is

```text
μ = q_* ((da × dk).withDensity (a,k ↦ ENNReal.ofReal (δ(a)⁻¹))).
```

The absolute value is the residue-cardinality normalization supplied by `T`,
not an arbitrarily scaled or base-extending absolute value. All ratios are
nonzero because their coordinates are units, so the modulus and its inverse
are positive. The density is the inverse modulus of the upper Borel. For
rank one the product over `i<j` is empty, hence the density is one.

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original notation on printed pp375–377 and the proof of Theorem 2.7 on
pp391–392 were read directly. Page 376 identifies the diagonal group,
multiplicative Haar measure and integral compact subgroup. Pages 376–377
specify the modular convention by converting right Haar to left Haar with
inverse modulus. In the proof of Theorem 2.7, p391 equation (3) uses the
factor `δ_r(a)⁻¹` after Iwasawa decomposition and compact-group finiteness.
Page 392 then applies the argument to absolute values to establish convergence
and justify the preceding formal integral manipulations.

This proposition is a derived measure-level formulation of the identity
invoked in that argument. Before using compact-group finiteness, Iwasawa
integration on the left quotient integrates a function of `[a k]` against
`δ(a)⁻¹ da dk`. The pushforward and density express exactly this identity
for nonnegative measurable functions, including functions with infinite
integral. Conversely, such an identity for all nonnegative measurable
functions determines the measure by taking indicators of measurable sets.
Measurability of the coordinate map and density is a consequence of their
continuous group and absolute-value constructions; checking this and proving
the measure identity are future proof obligations. The stated equality has
no complex integrability premise and therefore supports absolute-convergence
arguments. It is not restricted to compactly supported integrands.

Equation (4) on p391 subsequently writes the diagonal as
`diag(b₁⋯b_m, b₂⋯b_m, …, b_m)`. Those are simple-root and central coordinates.
The present statement uses the ordinary diagonal entries `a_i`, before that
reparameterization; it neither identifies the two coordinate systems nor
claims the associated change-of-variables formula here. The product of the
positive-root factors `|a_i/a_j|` is the upper-Borel modulus, obtained from
the conjugation scalars on strictly upper-triangular entries.

The mass-one choices are those of the published `RankinSelberg.Measures`,
not extra normalizations attributed to JPSS's notation. The theorems
`localMultiplicativeHaar_integerUnits`, `generalLinearHaar_integralSubgroup`
and `unipotentHaar_integral` give mass one to each integral-unit factor,
`K`, and `N ∩ K`, respectively. The compatibility predicate fixes the
quotient scale relative to the latter two measures. Accordingly there is
no free scalar in the conclusion. The normalization can be checked on the
image of `K`: averaging its indicator over `N` gives the indicator of that
image because `N ∩ K` has mass one, while ordinary diagonal integral units
have product mass one and modulus one. This explains the scalar choice;
formal extension of the Weil formula and this calculation remain part of
the future proof.

The published `UnipotentQuotient` construction and uniqueness theorem already
provide compatible measures with this scale. The algebraic
`GeneralLinear.Iwasawa.exists_iwasawa` supplies decompositions but does not
prove this integration identity. The missing analytic identity is precisely
the new target. All constructions in this file are local bindings within
its Prop-valued definition; no additional public non-Prop declarations or
changes to existing Library pairs are introduced.
