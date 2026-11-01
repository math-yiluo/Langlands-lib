# Normalized first-block quotient integration on determinant slices

Module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationStatement`.
Declaration `Langlands.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationStatement.{uF}`.
Author: Worker 823.

This closed proposition states the normalized measure disintegration
underlying JPSS (1983), Section 4.6, printed page 412, equation (6). It also
states the resulting Tonelli law, the absolute-integrability criterion and
the Bochner identity. The measure identity is the analytic content of the
source equation. The kernel packaging and the integrability criterion are
derived. This module supplies the statement only; its proof is a separate,
later obligation.

## Source equation (6)

JPSS define `G_r^m = {g : |det g| = q^(-m)}` on printed page 406, Section 4.2.
On printed page 412 they write `N_(t_1,t_2)` for the block-diagonal unipotent
matrices of display (5). With `r = t = t_1 + t_2`, equation (6) reads

```text
∫_{N_(t_1,t_2) \ G_r^m} f(g) dg
  = ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a.
```

The source gives no proof, no normalization of the three quotient measures and
no integrability conditions for `f`. The present proposition makes these
precise. The outer domain is the zero slice `L \ G^0` for every `k`. The inner
domain is the small slice `N_a \ GL_a^k`. The formula has no density and no
`k`-dependent scalar. The source ranks `t_1, t_2` are `a = m 0 + 1` and
`b = m 1 + 1`, and the source rank `r` is `t + 1` here. The source exponent
`m` is the integer `k` here, since `|det g| = q^(-k)` means `ord(det g) = k`.

## Quantifiers and canonical structures

The proposition quantifies over every prime `p` (through `Fact p.Prime`),
every `F : PadicField.{uF} p`, every `t : Nat`, every `m : Fin 2 → Nat`, and
every `h : ∑ i, (m i + 1) = t + 1`. Both block ranks are therefore positive
and add up to the total rank. The proposition installs the topology,
valuation, local-field structure, Hausdorff property and second countability
from `F.canonicalTopologicalData`, together with the general linear group
topologies of ranks `t + 1` and `a`. It has no representation, character,
Whittaker or convergence hypotheses.

The field, the groups `G`, `GL_a`, `GL_a^0`, `H`, `L`, both block unipotent
groups, and the three quotients carry Borel measurable structures. The finite
dependent product `BlockUnipotents m F.Carrier` keeps its product measurable
structure, and so does the binary product `GL_a^0 × N_b`. Their Borel
instances are inferred from second countability. For `GL_a` this is the
published `TopologicalData.generalLinearSecondCountableTopology`; for the
subgroups it comes through the subtype embedding.

All group, quotient, slice and fiber data are the published objects. Their
namespaces are `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient` (the
first-block data module, abbreviated `TwoBlockFirstBlock` in the task text),
`Langlands.RankinSelberg.TwoBlockUnipotentQuotient` and `Langlands.RankinSelberg`.

| Symbol | Actual object |
| --- | --- |
| `G` | `GeneralLinear (t + 1) F.Carrier` |
| `GA` | `GeneralLinear (m 0 + 1) F.Carrier`, that is `GL_a` |
| `Na`, `Nb` | `upperUnipotent (m 0 + 1) F.Carrier`, `upperUnipotent (m 1 + 1) F.Carrier` |
| `A0` | `TwoBlockFirstBlockQuotient.normOneSubgroup F (m 0 + 1)`, that is `GL_a^0 = ker |det|` |
| `H` | `TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier = N_(t_1,t_2)` |
| `L` | `TwoBlockFirstBlockQuotient.mixedSubgroup F h = diag(GL_a^0, N_b)` |
| `AQ` | `LeftUnipotentQuotient (m 0) F.Carrier = N_a \ GL_a` |
| `HQ` | `TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier = H \ G` |
| `LQ` | `TwoBlockFirstBlockQuotient.MixedQuotient F h = L \ G` |
| `N_a \ GL_a^k` | `RankinSelberg.determinantSlice T (m 0) k` |
| `H \ G^k` | `TwoBlockUnipotentQuotient.determinantSlice F h k` |
| `L \ G^0` | `TwoBlockFirstBlockQuotient.determinantSlice F h 0` |
| `fiberPoint q g` | `TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier q g`, the coset `[diag(u, 1) g]_H` for `q = [u]` |

Here `T = F.canonicalTopologicalData`. The fiber map is the published quotient
descent through `firstBlockEmbedding h F.Carrier`, `u ↦ diag(u, 1_b)`. The
proposition introduces no other quotient relation, chart or coset
representative.

## Fixed measures

The ambient and subgroup measures are

```text
μG  = generalLinearHaar F.Carrier t
μGA = generalLinearHaar F.Carrier (m 0)
μNa = unipotentHaar F.Carrier (m 0)
μNb = unipotentHaar F.Carrier (m 1)
μH  = Measure.map (blockUnipotentEquiv h F.Carrier)
        (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i))).
```

These are the published Haar measures that give mass one to the integral
points of each group. The proposition first asserts that `μH` is Haar and
regular.

It then asserts the existence of `μA0 : Measure A0` such that `μA0` is Haar,
`μA0` is regular, and

```text
Measure.map Subtype.val μA0 = μGA.restrict (A0 : Set GA).
```

Thus `μA0` is the restriction of `μGA` to the open subgroup `GL_a^0`. The
inclusion of an open subgroup is a measurable embedding, so this condition
determines `μA0` uniquely. The existential therefore chooses nothing. Every
later clause lies inside its scope. Put

```text
μL = Measure.map (mixedSubgroupEquiv F h) (μA0.prod μNb),
```

the transport of the product measure through the published multiplicative
equivalence `GL_a^0 × N_b ≃* L`. The proposition asserts that `μL` is Haar and
regular.

Next it asserts right invariance of `μNa`, `μH` and `μL`. These facts are
bound existentially as proofs and installed as instances for the remaining
clauses, because `QuotientIntegration.IsCompatible` uses them to define the
actual orbital averages. The proposition then asserts that compatible
quotient measures exist for the three fixed pairs:

```text
∃ νA, IsCompatible Na μGA μNa νA
∃ νH, IsCompatible H  μG  μH  νH
∃ νL, IsCompatible L  μG  μL  νL.
```

The universal clauses below therefore cannot hold vacuously. Compatibility is
exactly the published `IsCompatible`: the measure is nonzero, regular and
invariant under right translations, and it satisfies the Weil integral
formula, with integrability, for compactly supported continuous complex test
functions.

## Conclusions for every compatible triple

Let `νA`, `νH` and `νL` be any measures compatible with the three fixed pairs,
with `hA` the compatibility proof for `νA`. The proposition asserts that all
three are sigma-finite. For every integer `k` it sets

```text
hInvariant = normOneRightInvariant_of_isCompatible F (m 0) μGA μNa νA hA
νL0 = νL.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)
νHk = νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k).
```

The invariance proof comes from the published compatible-measure adapter.
The proposition then asserts the existence of a kernel
`κ : ProbabilityTheory.Kernel LQ HQ` with a proof of `IsSFiniteKernel κ`, such
that the following four clauses hold.

1. For every `g : G`, the representative formula is an equality of measures:

   ```text
   κ [g]_L = Measure.map (fun q => fiberPoint h F.Carrier q g)
               (νA.restrict (RankinSelberg.determinantSlice T (m 0) k)).
   ```

   This holds at every representative, not just almost everywhere. Its
   descent under left `L` is the published right-translation law: by
   `fiberPoint_mixedEmbedding_mul`, `fiberPoint q (diag(u, n) g)` equals
   `fiberPoint (q · u) g` for `u ∈ GL_a^0`. Right translation by `u` preserves
   `νA` (by `hInvariant`) and preserves the small slice, since
   `ord(det u) = 0`.
2. The measure identity, with Mathlib's kernel-measure composition:

   ```text
   κ ∘ₘ νL0 = νHk.
   ```

3. The Tonelli identity for every measurable `f : HQ → ℝ≥0∞`:

   ```text
   ∫⁻ q, ∫⁻ z, f z ∂κ q ∂νL0 = ∫⁻ z, f z ∂νHk.
   ```

4. For every measurable `f : HQ → ℂ`, the absolute-integrability criterion

   ```text
   Integrable f νHk ↔
     (∀ᵐ q ∂νL0, Integrable f (κ q)) ∧
     Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νL0,
   ```

   together with the Bochner law: if `Integrable f νHk`, then the published
   average `firstBlockAverage F h νA hInvariant k f` is integrable on `νL0`, and

   ```text
   ∫ z, f z ∂νHk = ∫ q, firstBlockAverage F h νA hInvariant k f q ∂νL0.
   ```

At `[g]_L` the published average is the total Bochner integral of
`q ↦ f (fiberPoint h F.Carrier q g)` over `N_a \ GL_a^k` against `νA`. For
measurable `f` this is `∫ z, f z ∂κ [g]_L`.

### Strength of the measurability assertions

The kernel type includes measurability of `[g]_L ↦ κ [g]_L`. Integrability
includes almost-everywhere strong measurability. The proposition asserts that
the first-block average is integrable on `νL0`, and so almost-everywhere
strongly measurable there. It does not assert Borel measurability of that
average. It does not claim convergence of the inner or outer integrals for
functions that are not integrable.

## Why one normalization works for every `k`

The following explains why the identity should hold with no `k`-dependent
factor. None of it is a premise. The proposition chooses no uniformizer and
assumes no translation identity; proving the proposition must establish these
facts.

* **Tower at the zero slice.** `H ≤ L` and `L / H ≅ GL_a^0 / N_a` through
  `mixedSubgroupEquiv`. The measure `μH` is the transport of `μNa × μNb`, and
  `μL` is the transport of `μA0 × μNb`. Because `μA0` is the restriction of
  `μGA` to the open subgroup `GL_a^0`, the fiber measure of `H \ L` is the
  restriction of `νA` to `N_a \ GL_a^0`. The Weil formulas for the three pairs
  then give the tower for `H \ G → L \ G`. For `g` with `ord(det g) = j`, every
  point `[diag(u, 1) g]_H` with `u ∈ GL_a^0` lies in `H \ G^j`. Restricting to
  `H \ G^k` therefore puts the outer variable in `L \ G^k` and the inner variable
  in `N_a \ GL_a^0`.
* **Shift to the source domains.** Choose `z ∈ GL_a` with `ord(det z) = k`, and
  put `d = diag(z, 1)`. Then `d` normalizes `L`, because
  `d diag(u, n) d⁻¹ = diag(z u z⁻¹, n)` and `GL_a^0` is normal in `GL_a`.
  Conjugation by `z` preserves `μGA`, since `GL_a` is unimodular. It also
  preserves `GL_a^0`, so it preserves the restricted measure `μA0`. Hence
  conjugation by `d` preserves `μL`. Since `G` is unimodular, left
  translation `[g]_L ↦ [d g]_L` is a measure-preserving bijection
  `L \ G^0 → L \ G^k` for `νL`. Under this shift the inner point becomes
  `[diag(u z, 1) g]_H`. Right translation by `z` on `N_a \ GL_a` maps
  `N_a \ GL_a^0` onto `N_a \ GL_a^k` and preserves `νA`. This yields the
  source domains: the outer `L \ G^0` and the inner `N_a \ GL_a^k`, with no
  factor.

A tower over the full quotient `L \ G` alone does not identify these source
domains. The shift step, which needs the normalization through restriction
on `GL_a^0`, is essential.

## Source and derived content

* **Source equation (6)** is the measure identity `κ ∘ₘ νL0 = νHk`, read through
  the representative formula. It is equivalently the Tonelli identity for
  nonnegative measurable functions, and the Bochner identity for integrable
  ones.
* **Derived packaging:** the explicit normalization of all measures, including
  existence and uniqueness of `μA0`; existence and sigma-finiteness of the
  compatible quotient measures; the s-finite measurable kernel; the
  absolute-integrability criterion; and integrability of the first-block
  average. The source states none of these. The kernel is a reformulation
  with no counterpart in the source.

## Source and scope

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, source ID `jpss-1983-rankin-selberg`. The registered PDF is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 406, 411 and 412 (one-based PDF pages 41, 46 and 47) were read
visually. The project literature notes record no errata for this source.

Outside this unit are source equation (7), section covariance with a
half-modulus factor, Fourier and Mellin identities, and factor identities. So
are the Section 9.3 lower-block disintegration and the tower `H \ G → N \ G` of
`TwoBlockUnipotentQuotientIntegrationStatement`. No downstream result is
assumed. The kernel and integration interfaces come from Mathlib's
`Probability/Kernel/Composition/MeasureComp.lean` and
`Probability/Kernel/Composition/IntegralCompProd.lean`. Their general
composition formulas do not establish the quotient-measure identity asserted
here.
