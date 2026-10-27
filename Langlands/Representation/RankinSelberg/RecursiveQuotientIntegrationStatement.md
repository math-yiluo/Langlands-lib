# Normalized recursive quotient integration

`Langlands.RankinSelberg.RecursiveQuotientIntegrationStatement` states the
recursive measure identity on the actual left quotient
`N_(n+2) \ GL_(n+2)(F)`, written in terms of the actual left quotient of rank
`n+1`. This module supplies one Prop-valued definition; it supplies no proof
of that proposition.

## Parameters and structures

The parameters are every prime `p` (through `[Fact p.Prime]`),
`F : PadicField.{uF} p` in an arbitrary universe `uF`, supplied
`T : F.TopologicalData`, and every natural number `n`, including zero. The
lower rank is `n+1` and the larger rank is `n+2`. For `n = 0` the lower
quotient is the actual rank-one quotient `LeftUnipotentQuotient 0 F.Carrier`
of `GL_1` by its trivial upper-unipotent subgroup; no separate case is made.

Inside the definition the topology, valuation and nonarchimedean local-field
structure are installed from `T` (`T.topology`, `T.valuativeRel`,
`T.localField`), as in `AnalyticStatement`. Borel measurable structures, with
their `BorelSpace` instances, are installed on

- the field units `F.Carrierˣ`;
- `GeneralLinear (n+1) F.Carrier` and `GeneralLinear (n+2) F.Carrier`;
- the actual subgroups `upperUnipotent (n+1) F.Carrier` and
  `upperUnipotent (n+2) F.Carrier`;
- the actual quotients `LeftUnipotentQuotient n F.Carrier` (rank `n+1`) and
  `LeftUnipotentQuotient (n+1) F.Carrier` (rank `n+2`).

The triple product carries Mathlib's existing product measurable structure
`Prod.instMeasurableSpace`, built from these Borel structures. No product
Borel structure or subtype structure is introduced.

The proposition then quantifies over both instances
`Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` and
`Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n+1))`, which the
compatibility predicate requires. It also quantifies over every pair of
actual measures

- `μsmall : Measure (LeftUnipotentQuotient n F.Carrier)` satisfying
  `QuotientIntegration.IsCompatible (upperUnipotent (n+1) F.Carrier)
  (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μsmall`, and
- `μlarge : Measure (LeftUnipotentQuotient (n+1) F.Carrier)` satisfying
  `QuotientIntegration.IsCompatible (upperUnipotent (n+2) F.Carrier)
  (generalLinearHaar F.Carrier (n+1)) (unipotentHaar F.Carrier (n+1)) μlarge`.

`IsCompatible` is the published predicate of `QuotientMeasure`. It requires
the measure to be nonzero, regular and right-translation invariant, and to
satisfy the Weil formula, with integrability, for continuous compactly
supported complex functions. No other normalization, integration,
decomposition or convergence hypothesis is added.

## Local bindings

The proposition uses the following local bindings:

```text
K = Conductor.integralSubgroup
      (ValuativeRel.valuation F.Carrier).integer (n+1)
dk = (generalLinearHaar F.Carrier (n+1)).restrict (K : Set _)
dMult = localMultiplicativeHaar F.Carrier
coordinates = recursiveQuotientCoordinates (F := F.Carrier) n
weight (q, a, k) =
  ENNReal.ofReal
    ((quotientDeterminantAbs (normalizedAbsoluteValue T) n q)⁻¹)
```

- `K` is the actual integral compact subgroup of `GL_(n+2)(F)`. (The index
  `n+1` of `Conductor.integralSubgroup` denotes matrices of size `n+2`.)
- `dk` is the measure on the ambient `GeneralLinear (n+2) F.Carrier`
  obtained by restricting the published Haar measure to `K`. It is supported
  on `K`, and no subtype transport is involved.
- `dMult` is the published multiplicative Haar measure on `F.Carrierˣ`.
- `coordinates` is the published `recursiveQuotientCoordinates n`. Its domain
  is the right-associated product
  `LeftUnipotentQuotient n F.Carrier × F.Carrierˣ × GeneralLinear (n+2) F.Carrier`,
  and it sends `(class g, a, k)` to the class of
  `rankInclusion 1 g * GeneralLinear.scalar a * k`, that is,
  `diag(g,1) · a · k` with `a` embedded as a scalar matrix and `k` arbitrary.
- `weight` depends only on the lower-quotient coordinate `q`. It is the
  inverse of `quotientDeterminantAbs (normalizedAbsoluteValue T) n q`, the
  published descent of `g ↦ |det g|`, so `weight` has exponent `-1`. The
  absolute value is `normalizedAbsoluteValue T`, the residue-cardinality
  normalization supplied by `T`. The value is positive because determinants
  of invertible matrices are nonzero. There is no power of `|a|` in the
  density.

## Conclusion

The exact conclusion is the measure identity

```text
μlarge =
  Measure.map coordinates
    ((μsmall.prod (dMult.prod dk)).withDensity weight).
```

The product is `μsmall × (dMult × dk)`, associated to the right like the
domain of `coordinates`. This is an equality of measures. It is not a Bochner
identity under an integrability premise, and it is not restricted to
compactly supported integrands. Hence it gives the identity

```text
∫ f dμlarge = ∫∫∫ f(coordinates (q, a, k)) · |det q|⁻¹ dμsmall(q) dMult(a) dk(k)
```

for every nonnegative measurable `f`, including functions with infinite
integral. Consumers can therefore use it to prove convergence. Conversely,
taking indicators of measurable sets shows that the identity for all such
`f` determines the measure. Proving that `coordinates` and `weight` are
measurable belongs to the future proof. Both maps are continuous: the
published `continuous_recursiveQuotientCoordinates` covers the first, and
the second is built from the determinant and the absolute value.

## Source and derivation

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 8.3, printed p449, equation (1) (one-based PDF page 84, zero-based
index 83) was read directly. Printed p448 introduces it with "Recall the
integration formula". The source writes

```text
∫_{N_r\G_r} F(g) dg
  = ∫_{N_(r-1)\G_(r-1) × Z_r × K_r} F[(g 0; 0 1) z k] |det g|^(-1) dg dz dk,
```

with representative `diag(g,1) z k`, where `z` lies in the centre `Z_r` and
`k` in the maximal compact subgroup `K_r`. Here `r = n+2`. The centre `Z_r`
is parametrized by `F.Carrierˣ` through `GeneralLinear.scalar`. The source
does not specify Haar normalizations at this point.

The proposition is a derived measure-level version of this formula, using
the project's published Haar choices. These choices are not attributed to
the source:

- `localMultiplicativeHaar_integerUnits`: the integral units have
  `dMult`-mass one;
- `generalLinearHaar_integralSubgroup`: the integral compact subgroup has
  mass one in each rank, so `dk` has total mass one;
- `unipotentHaar_integral`: the integral upper-unipotent subgroup has mass
  one in each rank;
- `IsCompatible` fixes the scale of `μsmall` and of `μlarge` relative to the
  corresponding group and unipotent measures.

For a standard derivation, write `P` for the mirabolic subgroup, whose last
row is `(0,…,0,1)`. Then `G_r = P Z_r K_r`. In the coordinates
`[[1, v], [0, 1]] · diag(g, 1)` the left Haar measure on `P` is
`|det g|^(-1) dv dg`. Integrating `v` together with `N_(r-1)` yields `N_r`.
This gives the formula up to one positive constant.

The displayed version has no free scalar because every measure in it is
already fixed. `dMult` and `dk` are fixed by the published mass-one
choices. `μsmall` and `μlarge` are fixed by compatibility: the published
`unipotentQuotientHaar_unique` shows that a compatible quotient measure is
unique in each rank. The density and the coordinates are fixed as well. So
the identity can hold for only one value of the constant, and the following
check shows that value is one. Test on the image of `K`. For `u ∈ N_r`, the
last row of `u · diag(g,1) · a` is `(0,…,0,a)`. Hence, for `k ∈ K`, the class
of `diag(g,1) a k` lies in the image of `K` exactly when `a` is an integral
unit and `g ∈ N_(n+1) K_(n+1)`. On that set `|det g| = 1`. Both sides
therefore give the image of `K` mass one. The left side gets this from
compatibility and the mass-one normalizations of `K` and of the integral
unipotents. The right side gets it from the same facts in rank `n+1` and
from mass one for the integral units and for `dk`. Formalizing this check,
and extending the Weil formula to the stated identity of measures, are proof
obligations, not conclusions of this statement.

## Scope

The published `RecursiveQuotientCoordinates` construction supplies descent,
continuity, the determinant formula `|det g| · |a|^(n+2) · |det k|` and the
last-row formula `a · lastRow k` for the representatives. It supplies no
measure identity. The published `UnipotentQuotient` construction provides
compatible quotient measures in every rank, so the hypotheses can be
satisfied.
The related `QuotientIwasawaIntegrationStatement` is a separate
ordinary-diagonal proposition and is not assumed here. This module states
the measure identity only. It proves no analytic estimate, and Whittaker
square estimates, holomorphy and local factors are outside it. All
constructions are local bindings inside the Prop-valued definition. The
module introduces no further public declarations and changes no existing
Library pair.
