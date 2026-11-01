# Linked lower mixed quotient integration in JPSS Section 4.9

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement`.
Closed declaration
`Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement.{uF}`.
Author: Worker 1196.

This proposition states the two measure disintegrations underlying JPSS
(1983), Section 4.9, equation (2), printed page 416, and equation (8),
printed page 418. The lower mixed subgroup has one Haar measure, normalized
to give its integral points mass one. Compatible measure existence,
normalization, measurable kernels, Tonelli and absolute integrability are
conclusions. The proposition is a statement; no analytic proof is supplied.

## Original source and derived content

The registered original is `jpss-1983-rankin-selberg`: H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg convolutions*,
American Journal of Mathematics 105 (1983), 367–464,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 412–413 and 416–418 were read from the scan; these are
one-based PDF pages 47–48 and 51–53. No applicable registered erratum was
found in the project source index and notes.

Printed page 412, Section 4.6 display (5), specifies the block diagonal
unipotent group, and printed page 413 specifies the lower block unipotent
group. Section 4.9 equation (2) integrates over the rectangular lower
radical, with outer domain `L \ G^0`; the group `L` is defined immediately
below that formula. Equation (8) uses the same outer quotient and
first-block fibers, with positive density `|det v|^b`.

The source displays do not specify the normalization and measure-theoretic
hypotheses used here. The shared mass-one normalization, compatible
quotient existence and transport, arbitrary supplied rectangular Haar,
per-slice density, kernel formulation and absolute-integrability criteria
are derived packaging of those formulas. Section 4.6 equation (6), on
printed page 412, concerns a different outer subgroup and has no such
density. It does not supply the present equation (8).

## Quantifiers, topology and actual domains

The proposition quantifies over every prime `p` through `Fact p.Prime`,
every canonical `F : PadicField.{uF} p`, every `t : Nat`, every
`m : Fin 2 → Nat` and every `h : ∑ i, (m i + 1) = t + 1`.
Put `T = F.canonicalTopologicalData`, `a = m 0 + 1`, `b = m 1 + 1`.
The blocks are arbitrary positive sizes, including size one, and the field
universe is arbitrary. There are no representation or character inputs.

All topology, valuation and local-field instances are canonical. The
field, groups and quotients have their Borel measurable structures.
The rectangle `R = Matrix (Fin b) (Fin a) F.Carrier`, the product
`A0 × Nb`, and the coordinate product `R × (A0 × Nb)` retain their actual
product measurable structures. Their Borel instances follow from
second countability; these measurable spaces are not replaced by
independently chosen Borel spaces.

All objects below are imported from the published first-block,
lower-unipotent and lower mixed data modules.

| Symbol | Actual object |
| --- | --- |
| `G`, `GA` | `GeneralLinear (t + 1) F.Carrier`, `GeneralLinear a F.Carrier` |
| `A0` | `TwoBlockFirstBlockQuotient.normOneSubgroup F a` |
| `Na`, `Nb`, `N` | `upperUnipotent a F.Carrier`, `upperUnipotent b F.Carrier`, `upperUnipotent (t + 1) F.Carrier` |
| `M` | `TwoBlockFirstBlockQuotient.mixedSubgroup F h = diag(GL_a^0,Nb)` |
| `Hminus` | `TwoBlockLowerUnipotentQuotient.lowerBlockUnipotent h F.Carrier` |
| `Lminus` | `TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup F h` |
| `MQ` | `TwoBlockFirstBlockQuotient.MixedQuotient F h = M \ G` |
| `HQ` | `TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier = Hminus \ G` |
| `LQ` | `TwoBlockLowerFirstBlockQuotient.LowerMixedQuotient F h = Lminus \ G` |
| `AQ`, `NQ` | `LeftUnipotentQuotient (m 0) F.Carrier`, `LeftUnipotentQuotient t F.Carrier` |

In the lower mixed namespace, `P_M = projectionFromMixed F h` and
`P_H = projectionFromLower F h` are the actual projections to `LQ`.
Their measurability and exact preimage identities for every determinant
slice are included. These are already established data facts, not
disintegration premises.

`LQ0 = TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0`,
`MQ0 = TwoBlockFirstBlockQuotient.determinantSlice F h 0`,
`HQk = TwoBlockLowerUnipotentQuotient.determinantSlice F h k`, and
`AQk = RankinSelberg.determinantSlice T (m 0) k` are the actual published
slices. The outer domain in both formulas is `LQ0`. For `k ≠ 0`, a
first-block fiber point has order `k` and its image under `P_H` does too;
it is not claimed to project to the order-zero base point.

## Shared normalizations and compatible quotient existence

Set

```text
μG  = generalLinearHaar F.Carrier t
μGA = generalLinearHaar F.Carrier (m 0)
μNa = unipotentHaar F.Carrier (m 0)
μNb = unipotentHaar F.Carrier (m 1)
μN  = unipotentHaar F.Carrier t.
```

These are the published integral-points mass-one Haar measures.
The proposition asserts their Haar and regularity certificates.
It asserts existence of a regular Haar measure `μA0` on the actual
open norm-one subgroup `A0` satisfying

```text
Measure.map Subtype.val μA0 = μGA.restrict (A0 : Set GA).
```

Define

```text
μM = Measure.map (TwoBlockFirstBlockQuotient.mixedSubgroupEquiv F h)
       (μA0.prod μNb)
μHminus = Measure.map
  (TwoBlockLowerUnipotentQuotient.conjugationEquiv h F.Carrier).symm μN.
```

Their Haar and regularity properties are conclusions. The subgroup
equivalence is conjugation by
`Crot = ((succBlockShape m h).reverseMatrix F.Carrier)⁻¹`, with
representative law `x ↦ Crot*x*Crot⁻¹`. Its inverse is used in `μHminus`.

There exists a regular Haar measure `μL` on the actual subgroup `Lminus`
with

```text
μL (Subtype.val ⁻¹' (Conductor.integralSubgroup O t : Set G)) = 1,
O = (ValuativeRel.valuation F.Carrier).integer.
```

All these measures have right-invariance certificates, existentially
bound as proofs and installed as instances for compatibility and orbital
averages. These are conclusions, not assumptions on the input field.

For every supplied additive Haar measure `μR` on the actual Borel
rectangle, put `c = μR {Z | ∀ i j, Z i j ∈ O} : ENNReal`.
The proposition asserts `0 < c`, `c < ⊤`, and

```text
Measure.map chi (μR.prod (μA0.prod μNb)) = c • μL,
chi = TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupHomeomorph F h.
```

The published law is
`chi (Z,(a0,n)) = Rlower(Z) * mixedEmbedding F h (a0,n)` as an element
of `Lminus`, where `Rlower` is the published lower radical. The same
`μL` is quantified before every `μR`; the input measure is never rescaled
inside a fiber integral.

Compatible measures exist for all four exact pairs:

```text
νA : (μGA, μNa) on AQ
νM : (μG,  μM)  on MQ
νL : (μG,  μL)  on LQ
νN : (μG,  μN)  on NQ.
```

Compatibility is exactly `QuotientIntegration.IsCompatible`, including
nonzero regular quotient measure, right-translation invariance and the
Weil formula with integrability for compactly supported continuous
complex test functions. For every compatible quadruple the proposition
asserts sigma-finiteness and sets

```text
νMinus = Measure.map
  (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN.
```

This transported measure is sigma-finite and compatible with
`(μG,μHminus)`. Here the quotient equivalence is left multiplication:
`[g]_Hminus ↦ [Crot*g]_N`. It is distinct from subgroup conjugation.
All subsequent assertions hold for every compatible choice; the explicit
existence clauses prevent vacuity.

## Equation (2): rectangular fibers

Write `νL0 = νL.restrict LQ0` and `νM0 = νM.restrict MQ0`.
For every supplied `μR` there is a measurable s-finite kernel
`κR : Kernel LQ MQ`, with equality of measures at every representative:

```text
κR [g]_Lminus =
  Measure.map
    (fun Z => TwoBlockLowerFirstBlockQuotient.radicalFiberPoint F h Z g) μR.
```

The actual fiber point is `[Rlower(Z)*g]_M`. Kernel measurability is
part of `Kernel`, and s-finiteness is the explicit `IsSFiniteKernel`
certificate. The measure and Tonelli identities are

```text
κR ∘ₘ νL0 = c • νM0
∫⁻ q, ∫⁻ z, f z ∂κR q ∂νL0 = c * ∫⁻ z, f z ∂νM0
```

for every measurable `f : MQ → ENNReal`. For every measurable complex
`f`, the proposition states the equivalence

```text
Integrable f νM0 ↔
  (∀ᵐ q ∂νL0, Integrable f (κR q)) ∧
  Integrable (fun q => ∫ z, ‖f z‖ ∂κR q) νL0.
```

If `f` is integrable, the actual published total descended function
`TwoBlockLowerFirstBlockQuotient.radicalAverage F h μR f` is
almost everywhere strongly measurable and integrable on `νL0`, and

```text
∫ q, radicalAverage F h μR f q ∂νL0 = c.toReal • ∫ z, f z ∂νM0.
```

The factor has this direction because the coordinate measure has mass
`c` on the integral subgroup while `μL` has mass one. Consequently the
unscaled iterated fiber measure is `c` times the mixed quotient measure.

## Equation (8): first-block fibers and positive density

For every integer `k`, let

```text
d = ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
hInvariant =
  TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible
    F (m 0) μGA μNa νA hA.
```

Here `hA` is the compatibility proof for the supplied `νA`.
The proposition asserts `0 < d`, `d < ⊤` and, for every `v : GA`
whose small quotient lies in `AQk`,

```text
d = (ENNReal.ofReal (T.normalizedAbs (det v))) ^ b.
```

Thus the density is `|det v|^b = q^(-k*b)`, with positive exponent
`b`, arising from the first-block action on the lower radical. It
is constant on the small slice.

There is a measurable s-finite kernel `κA : Kernel LQ HQ` for each `k`
such that, for every `g : G`,

```text
κA [g]_Lminus =
  Measure.map
    (fun q => TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint F h q g)
    (νA.restrict AQk).
```

At `q = [v]`, the actual fiber point is `[diag(v,1)*g]_Hminus`.
Put `νMinusk = νMinus.restrict HQk`. The identities are

```text
d • (κA ∘ₘ νL0) = νMinusk
∫⁻ z, f z ∂νMinusk = d * ∫⁻ q, ∫⁻ z, f z ∂κA q ∂νL0
```

for every measurable `f : HQ → ENNReal`. For every measurable complex
`f`, the proposition states

```text
Integrable f νMinusk ↔
  (∀ᵐ q ∂νL0, Integrable f (κA q)) ∧
  Integrable (fun q => ∫ z, ‖f z‖ ∂κA q) νL0.
```

When `f` is integrable, the published
`TwoBlockLowerFirstBlockQuotient.firstBlockAverage F h νA hInvariant k f`
is almost everywhere strongly measurable and integrable on `νL0`, and

```text
∫ z, f z ∂νMinusk =
  d.toReal • ∫ q, firstBlockAverage F h νA hInvariant k f q ∂νL0.
```

The first-block average remains the unweighted total average of the data
module. Its density occurs only in the displayed scalar. There is no
rectangular cube factor in this equation for the shared normalization.

## Strength and boundaries

Both absolute-integrability equivalences are conclusions; equalities of
total Bochner integrals alone would not imply them. The averages are
total integrals defined by actual quotient descent. Their asserted
outer strong measurability is almost everywhere under integrability,
not unconditional Borel measurability for arbitrary complex functions.
All integer slices and every supplied rectangular Haar are retained.

The proposition assumes no uniformizer, disintegration, convergence or
functional equation. It claims no representation-specific convergence,
Laurent-series identity, Section 4.8 duality, block functional equation,
factor existence or gamma/L multiplicativity. It uses neither Section
9.3 nor Section 7 assembly nor the dominant analytic base. The two
analytic disintegrations and their supporting existence/normalization
claims remain to be proved separately.
