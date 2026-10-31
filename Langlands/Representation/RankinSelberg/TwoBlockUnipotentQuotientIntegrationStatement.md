# Normalized integration for the two-block unipotent quotient tower

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`.
Declaration `Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement.{uF}`.
Author: Worker 113.

This closed proposition states the quotient-measure identity and absolute-integrability
control underlying the first unfolding in JPSS (1983), Section 4.6. It is derived
analytic infrastructure, rather than a verbatim numbered theorem in the source.
This module supplies the statement; its proof is a subsequent obligation.

## Quantifiers and canonical structures

The proposition quantifies over every prime `p` (through `Fact p.Prime`), every
`F : PadicField.{uF} p`, every `t : Nat`, every `m : Fin 2 → Nat`, and every
`h : ∑ i, (m i + 1) = t + 1`. Thus both block ranks are positive and their
sum is the total rank. It installs the topology, valuation, local-field
structure, Hausdorff property and second countability from
`F.canonicalTopologicalData`, and the corresponding general linear group
topology. There are no representation, character, Whittaker or convergence
hypotheses.

The field, groups and quotients carry their Borel measurable structures.
Each block unipotent group carries its Borel structure; the finite dependent
product `BlockUnipotents m F.Carrier` retains its actual product measurable
structure. The rectangle
`R = Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier` also retains its actual
product measurable structure. The Borel instances on these products are
inferred using canonical second countability; neither product measurable
structure is replaced by a separate choice.

The block second-countability certificates use the published
`TopologicalData.generalLinearSecondCountableTopology` and the subgroup
subtype embedding. This supplies the product Borel instance directly.

All quotient data comes unchanged from the published namespace
`Langlands.RankinSelberg.TwoBlockUnipotentQuotient`:

| Symbol | Actual object |
| --- | --- |
| `G` | `GeneralLinear (t + 1) F.Carrier` |
| `N` | `upperUnipotent (t + 1) F.Carrier` |
| `H` | `blockUnipotent h F.Carrier`, the block-diagonal unipotent subgroup |
| `NQ` | `LeftUnipotentQuotient t F.Carrier = N \ G` |
| `HQ` | `BlockQuotient h F.Carrier = H \ G` |
| `pi` | `projection h F.Carrier : HQ → NQ` |
| `u(x)` | `TwoBlockJacquet.upperRadical h F.Carrier x` |
| `fiberPoint x g` | the actual coset `[u(x) g]_H` |

## Fixed group measures and existence

The fixed measures are

```text
muG = generalLinearHaar F.Carrier t
muN = unipotentHaar F.Carrier t
muH = Measure.map (blockUnipotentEquiv h F.Carrier)
        (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i))).
```

The general linear and full unipotent measures are the published measures
normalized to give their integral subgroups mass one. Each block unipotent
measure is normalized in the same way. Their product is transported to `H`
by the published multiplicative equivalence, whose canonical topology is a
multiplicative homeomorphism. In particular, `muH` is fixed before, and
independently of, the rectangular measure.

The first conclusions assert that `muH` is Haar and regular, and that both
`muN` and `muH` are right invariant. The latter conclusions are existentially
bound as proofs and installed as instances for the remaining clauses, since
`QuotientIntegration.IsCompatible` uses right invariance to define actual
orbital averaging. The proposition then asserts existence of a compatible
quotient measure on each of `NQ` and `HQ` for the fixed measures. The later
universal assertions about compatible measures therefore have actual
existence conclusions as well.

Here compatibility is precisely the published `IsCompatible`: it includes
nonzero regularity, invariance under right translations, and the Weil
integral formula, with integrability, for compactly supported continuous
complex test functions. It is not replaced by an assumed nonnegative tower
formula.

## Rectangular scale and the fiber kernel

For every supplied `muR : Measure R` satisfying `muR.IsAddHaarMeasure`, set

```text
O = (ValuativeRel.valuation F.Carrier).integer
c = muR {x | forall a b, x a b ∈ O} : ENNReal.
```

The conclusions include `0 < c` and `c < top`. The measure `muR` is used
unchanged throughout. This includes every published `rectangularMeasure`
from a supplied scalar self-dual Haar measure; no scalar normalization or
mass-one condition is imposed on it.

For each such `muR`, the proposition existentially binds an actual
`ProbabilityTheory.Kernel NQ HQ`, written `kappa`, and a proof that it is an
`IsSFiniteKernel`. For every `g : G`, its representative law is an equality
of actual measures:

```text
kappa [g]_N = Measure.map (fun x => fiberPoint h F.Carrier x g) muR.
```

The kernel type includes measurability in the base point. The law is
required at every representative, rather than only almost everywhere, and
the same kernel works for all compatible quotient measures and slices.
The published `projection_fiberPoint` places these measures in the actual
fibers of `pi`.

The normalization factor has the following coordinate explanation. In
coordinates `(a,x) ↦ a * u(x)` from `H × R` to `N`, integral points correspond
to integral block unipotent elements and integral rectangular matrices.
Their mass under `muH.prod muR` is `c`, since the two integral block groups
have mass one. Their mass under `muN` is one. Thus the transported coordinate
measure must be `c` times `muN`, which gives the factor direction below.
The future proof must justify this coordinate measure transport; it is not
a premise of the proposition. In particular, the proposition does not set
`c = 1` or rescale either `muH` or the supplied `muR`.

## Restricted tower, Tonelli and absolute integrability

For every pair of measures `nuN : Measure NQ` and `nuH : Measure HQ`
compatible with `(muG,muN)` and `(muG,muH)` respectively, the proposition
asserts `SigmaFinite nuN` and `SigmaFinite nuH`. For every Borel measurable
set `s : Set NQ`, write

```text
nuNs = nuN.restrict s
nuHs = nuH.restrict (pi ⁻¹' s).
```

The restricted measure identity is Mathlib's actual kernel-measure composition:

```text
kappa ∘ₘ nuNs = c • nuHs.
```

Taking `s = univ` gives the whole-space tower. Taking any of the published
measurable determinant slices gives the corresponding slice identity; its
preimage is the published determinant slice on `HQ`.

For every measurable `f : HQ → ENNReal`, the nonnegative Tonelli formula is

```text
(lintegral q, lintegral z, f z dkappa(q) dnuNs) =
  c * (lintegral z, f z dnuHs).
```

For every measurable `f : HQ → Complex`, the absolute-integrability criterion is

```text
Integrable f nuHs ↔
  (forall-ae q under nuNs, Integrable f (kappa q)) ∧
  Integrable (fun q => integral z, norm (f z) dkappa(q)) nuNs.
```

The inner norm integral here is real valued. When this same measurable `f`
is integrable under `nuHs`, the conclusions further assert integrability of
the actual published function `radicalAverage F h muR f` under `nuNs`, and

```text
(integral q, radicalAverage F h muR f q dnuNs) =
  c.toReal • (integral z, f z dnuHs).
```

The right side uses the real scalar action on complex numbers. Thus this
last formula is accompanied by genuine integrability conclusions, rather
than an equality alone between totalized Bochner integrals. It uses the
published descended radical average without defining a new averaging
operation.

## Source and scope

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, source ID `jpss-1983-rankin-selberg`. The registered PDF is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 410–412 (zero-based PDF indices 44–46, one-based pages 45–47)
were read visually. No applicable source errata note was found in the
project notes.

On printed page 411, equation (4) integrates over `N \ G^k` and the upper
radical. The first integral on printed page 412 is over `H \ G^k`, with
`H = N_(t1,t2)` defined by the block-diagonal matrices in display (5).
The source ranks `t1,t2` correspond to `m 0 + 1,m 1 + 1`; its total rank
is `t + 1` here. The source obtains an unweighted fiber average after
character cancellation in its representation-specific integrand. The
present proposition isolates the representation-free analytic measure
identity with the supplied measure scale made explicit.

It asserts no integrability of future Whittaker, Jacquet or Schwartz
integrands, no comparison of arbitrary functionals, and no factor-existence
or multiplicativity result. The later disintegration through the first-block
general linear subgroup in page 412 equation (6) is a separate obligation.
None of these downstream assertions is assumed to obtain this infrastructure.
The imported kernel and integration interfaces are Mathlib's
`Probability/Kernel/Composition/MeasureComp.lean` and
`Probability/Kernel/Composition/IntegralCompProd.lean`; their general
composition formulas do not themselves establish the quotient-measure
transport required by this statement.
