# Reflection in the real equal-rank dual integral

The main internal proposition is
`Langlands.Global.RankinSelbergGlobal.RealPlaceReflectionReductionStatement.{u}`:

```text
RealJacquetRestrictionEquationStatement.{u} →
RealPairCentralCompatibilityStatement.{u} →
RealPlaceFunctionalEquationStatement.{u}.
```

The theorem `realPlaceReflectionReduction` proves this implication. The
earlier `RealJacquetConventionReduction` required the additional premise
`RealEqualDualReflectionStatement`. This module proves that premise
unconditionally as `realEqualDualReflection`, using actual global restrictions,
the compact scalar action, and the supplied quotient measure. The full
functional-equation target remains open because the two displayed premises
remain open.

This internal development proves reflection of the equal-rank quotient integral
under right multiplication by minus identity. It treats the chosen quotient
representatives explicitly: the group kernel descends because its pair
product, last row and determinant weight are invariant under the upper
unipotent subgroup.

The Fourier transform with parameter `-a` is the transform with parameter `a`
at the negative argument. The right quotient translation preserves every
supplied compatible quotient measure. A pair product with central scalar
`k`, where `k² = 1`, therefore gives both integrability equivalence of the
two reflected kernels and the equality of their total Bochner integrals
with multiplier `k`.

More precisely, `RealPlaceReflection.kernel` is
`P(g) Φ(lastRow(g)) detPower(realNormalizedAbs, g, s)`. The group kernel is
left upper-unipotent invariant whenever `P` is. The proof
`kernel_out_rightTranslate` uses the genuinely descended function and
`Quotient.out_eq` to show that evaluation at the chosen representative after
right translation equals evaluation at `q.out * z`. It does not assume that
the chosen representatives themselves commute with right translation.

Right multiplication by minus identity negates the last row and leaves the
absolute determinant, hence its complex spectral weight, unchanged. The
previously proved `RealJacquet.fourier_neg` identifies the transform with
parameter `-a` with the transform with parameter `a` evaluated at the negative
argument. If `P(g (-1)) = k P(g)` and `k² = 1`, these identities give

```text
K_minus(q) = k * K_plus(q (-1)).
```

The field `D.compatible.right_invariant (-1)` is the measure-preserving
translation needed for change of variables. Its homeomorphism is a measurable
embedding. Since `k² = 1` implies `k ≠ 0`, multiplication by `k` preserves
integrability. The measure-preserving composition laws and constant
homogeneity of the total Bochner integral then prove
`Integrable K_minus ↔ Integrable K_plus` and
`integral K_minus = k * integral K_plus`. This generic calculation holds for
every complex `s` and every function `Φ` on the row space; it needs no
regularity or convergence assumption on `Φ`.

For the actual dual integrals, take
`P(g) = W̃(g) W̃'(g)` and
`k = realMinusOneScalar T v * realMinusOneScalar T' v`.
The companion `RealPlaceWhittakerCovariance` gives left unipotent invariance
and the two central covariance identities. `realMinusOneScalar_sq` gives
`k² = 1`. The unitary adelic character, together with rational triviality,
satisfies `IsStandardAdditiveCharacter`, as checked in
`RealPlaceReflection.unitary_isStandard`. Thus the construction applies to
every datum quantified by `RealEqualDualReflectionStatement`, including every
compatible quotient measure, every rank index `r` with `r = 0` allowed, and
every number-field universe `u`. Contragredient and parameter hypotheses in
that existing statement are retained but are unnecessary for this reflection
calculation.

The two remaining premises have exactly their previous meanings.
`RealJacquetRestrictionEquationStatement` retains both local analytic packages
for the actual global restrictions: convergence, holomorphy, meromorphic
continuation, the source-convention equations, local-model membership and
normalization identification. `RealPairCentralCompatibilityStatement` retains
the equality of the pair-parameter determinant at minus one with the specified
powers of the two actual compact scalars. Neither premise follows from the
reflection calculation. The final proof feeds these two hypotheses and
`realEqualDualReflection` to `realPlaceJacquetConventionReduction`.

No convergence or analytic continuation theorem is used in this calculation.
Its provenance is internal: it is derived from the existing actions, Whittaker
integrals, Fourier identity and quotient-measure compatibility fields. The
analytic source conventions motivating the earlier reduction are documented
in its own paired Markdown; no further analytic theorem is quoted here.
