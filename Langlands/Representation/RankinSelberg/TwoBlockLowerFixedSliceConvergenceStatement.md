# Absolute convergence on every determinant slice of the Section 4.7 lower quotient

Module
`Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement`,
namespace `Langlands.RankinSelberg`. Author: Worker 86.

The closed proposition
`TwoBlockLowerFixedSliceConvergenceStatement.{uF,uV,uW}` states absolute
convergence of the actual lower-quotient integral in JPSS Section 4.7 on
every determinant slice, for sufficiently large opposite real twists. It
also states the compatible-measure existence and transport facts needed
to specify the normalization. This module defines a proposition and
supplies no proof of it.

## Source and scope

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg convolutions*, American Journal of Mathematics
105 (1983), 367–464, source ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained Central-Library scan was read visually at printed pages
412–414 and 416–418. In this scan these are one-based PDF page numbers
47–49 and 51–53, respectively. The project source and public-note
inventories contain no registered erratum for this source.

Equation (4.7.1), printed page 412, has a lower integral over
`H_(t₁,t₂) \ G_r` with integrand

```text
f[g; e, e] W(w' g) |det g|^s (gΦ)~(ζ, η),
w' = w_r diag(w_(t₁), w_(t₂)).
```

Page 413 defines the subgroup, rows and first-block partial Fourier
transform, and asserts convergence after restriction to `G_r^k` for
`u ≫ 0`. Page 414 proves absolute convergence by majorization. The present
statement concerns the unweighted integrand on each such slice.
The determinant weight is a finite constant on a fixed slice, so omitting
it preserves absolute integrability there.

The source's convergence assertion is the analytic content.
Measurability, explicit compatible-measure existence, sigma-finiteness,
and transport of both restricted integrals are derived measure-theoretic
packaging of that content. They are asserted here as conclusions rather
than supplied as premises. Sections 4.9, printed pages 416–418, use the
already established convergence in a separate functional-equation
calculation and two integration formulas. Those arguments are not
statements of this module.

## Complete parameters and their order

The definition has no external parameters. Its only universe parameters
are the independent `uF`, `uV` and `uW`.

1. `p : ℕ`, `[Fact p.Prime]`, and every `F : PadicField.{uF} p`.
   Write `T = F.canonicalTopologicalData`. The topology, valuation,
   local-field structure, Hausdorff structure and second countability
   are canonical. The measurable structures of the field, group,
   subgroup and both quotient spaces are explicitly their Borel
   sigma-algebras.
2. Every `ψ : UnitaryAdditiveCharacter F.Carrier` and every supplied
   `ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ`. The character type
   includes continuity, unitary values and nontriviality. The inner
   Fourier integral uses exactly `ν.val`; no Haar measure is selected
   or rescaled.
3. `t : ℕ`, `m : Fin 2 → ℕ`, and
   `h : ∑ i, (m i + 1) = t + 1`. Thus the block ranks are
   `a = m 0 + 1` and `b = m 1 + 1`, and the total rank is `t + 1`.
   Either block can have rank one and the ranks may differ.
4. A right-invariance certificate for the exact unipotent Haar measure
   is asserted to exist. With that certificate installed, the statement
   asserts compatible standard quotient measure existence and, for every
   compatible measure, sigma-finiteness of it and its prescribed lower
   transport.
5. Every `V : Type uV`, `[AddCommGroup V]`, `[Module ℂ V]`, and actual
   `π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V`,
   followed by its full standard Whittaker-type hypothesis and every
   `lambda : glFunctionals ψ t π`.
6. Every dependent carrier family `W : Fin 2 → Type uW`, with its
   complex module structures; every actual block representation
   `τ i` of `GL_(m i + 1)(F)` on `W i`; the full standard
   Whittaker-type hypothesis for each block; and every supplied
   `ell i : glInverseFunctionals ψ (m i) (τ i)`.
7. There exists one `C : ℝ`. For every `u : ℝ` with `C < u`,
   every compatible `νN`, every section `f` of the actual lower
   induction of `twoBlockOppositeTwistBlocks F m τ u`, every
   `Wtest : (Whittaker.coefficientModel π lambda).toSubmodule`,
   every row Schwartz–Bruhat function `Φ`, and every `k : ℤ`,
   the analytic conclusions below hold.

The threshold may depend on all data preceding it, including `π`,
its full Whittaker-type hypothesis and `lambda`, as well as the
blocks and their supplied functionals. It precedes `u`, `νN`, `f`,
`Wtest`, `Φ` and `k`, so one threshold works for all of them.
The universal measure quantifier in item 4 belongs to the separate
sigma-finiteness conjunct; it does not scope over `C`.

Here full standard Whittaker type is precisely the published
`IsOfWhittakerType n (standardCharacter ψ n) ρ`: admissibility,
finite generation of `ρ.asModule` over the actual complex group
algebra, and a linear equivalence between the standard-functional
space and `ℂ`. This allows reducible representations. There are no
nonvanishing conditions on `lambda` or `ell`; in particular zero
functionals, zero sections, zero coefficients and zero Schwartz
functions remain within the scope. The coefficient model is the
actual image of `v ↦ (g ↦ lambda (π g v))`, not the space of arbitrary
functions satisfying only Whittaker covariance.

## The exact function and quotient

The lower quotient is the published
`HQ = TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier`,
the left quotient of `G = GL_(t+1)(F)` by
`Hminus = {[[n_a,0],[X,n_b]]}`. Put `B = succBlockShape m h` and

```text
Crot = TwoBlockLowerUnipotentQuotient.blockRotation h F.Carrier
     = (B.reverseMatrix F.Carrier)⁻¹.
```

For the opposite real twists `(-u,+u)`, use exactly the published
`twoBlockOppositeTwistBlocks F m τ u` and the supplied-functional
transport

```text
ell_u i = twoBlockOppositeTwistFunctional F m ψ τ u i (ell i).
E = TwoBlockLowerUnfolding.integrand ell_u f Wtest.val Φ ν.val.
```

The published representative law `TwoBlockLowerUnfolding.integrand_mk`
gives, for every `g : G`,

```text
E [g] = Wtest.val.val (Crot * g) *
  TwoBlockJacquet.scalarSection (fun i => (ell_u i).val) f g 1 *
  TwoBlockLowerUnfolding.partialSection h ψ ν.val Φ g.
```

In the last factor the transform has the plus sign, integrates the first
block, uses the source rows `ζ = (1,0,…,0)` and `η = (0,…,0,1)`, and uses
the finite product of copies of the exact supplied `ν.val.measure`.
The statement imports this actual descended function; it introduces no
representative choice, replacement subgroup or replacement Fourier
operation. The underlying linear map of `ell_u i` is the supplied
`(ell i).val`.

## Measures and analytic conclusions

The standard quotient is `NQ = LeftUnipotentQuotient t F.Carrier`,
with `N = upperUnipotent (t + 1) F.Carrier`. Set exactly

```text
μG = generalLinearHaar F.Carrier t,
μN = unipotentHaar F.Carrier t.
```

These are normalized by mass one on the respective integral subgroups.
The statement asserts
`∃ hN : Measure.IsMulRightInvariant μN` and, with `hN` installed,
`∃ νN : Measure NQ, QuotientIntegration.IsCompatible N μG μN νN`.
Compatibility is the published property of the actual measure: nonzero,
regular, invariant under right translations, with the integrable Weil
formula on compactly supported continuous complex functions.
Existence is a conclusion and the subsequent claims apply to every
compatible `νN`.

For each such measure, define exactly

```text
νMinus = Measure.map
  (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN.
```

Both `νN` and `νMinus` are asserted sigma-finite, independently of the
representation data. The map `lowerToStandard` is the published
homeomorphism on the canonical quotient topologies taking `[g]` to
`[Crot * g]`. Its inverse takes `[g]` to `[Crot⁻¹ * g]`; this transport
is left multiplication on representatives. No quotient-conjugation map
or independently normalized lower measure appears.

For every `u > C`, section, actual coefficient, `Φ` and integer `k`,
write

```text
lowerSlice = TwoBlockLowerUnipotentQuotient.determinantSlice F h k,
standardSlice = RankinSelberg.determinantSlice T t k,
Estandard q = E ((lowerToStandard h F.Carrier).symm q).
```

The five conjuncts are exactly:

- `Measurable E` for the canonical Borel structure on `HQ`.
- `Integrable E (νMinus.restrict lowerSlice)`.
- `Integrable Estandard (νN.restrict standardSlice)`.
- Equality of the complex Bochner integrals of `E` and `Estandard`
  for those respective restricted measures.
- Equality of the real integrals of `‖E‖` and `‖Estandard‖` for those
  same restricted measures.

`Integrable` includes a.e. strong measurability and finite norm integral.
The two integrability conclusions establish actual absolute convergence;
the equalities between total Bochner integrals alone would not do so.
The public slice correspondence identifies the inverse image of the
lower slice with the standard slice. Together with the Borel
homeomorphism, it explains the derived transport equalities and the
absence of an extra normalization factor.

## Why the source supports this bound

On page 413 the source uses an Iwasawa integration formula for
`Hminus \ G_r^k`: integration over a compact group and a diagonal
determinant slice, with a fixed positive quasi-character density.
Smooth sections and Whittaker coefficients, and locally constant row
Schwartz functions, reduce the compact integration to finitely many
terms. Row Schwartz–Bruhat functions decompose into finite sums of
coordinate tensors `Φ₁ ⊗ ⋯ ⊗ Φ_r`. Evaluating the first-block
partial Fourier integral reduces the row factor to a Schwartz function
of `(a₁⁻¹,a_r)` and a positive quasi-character density, giving
(4.7.3) on page 414.

The section estimate (4.7.4), derived from the block estimates of
Section 4.6, bounds its absolute value by

```text
|det a_first|^(-u) |det a_second|^u η(a),
```

where `η` is a finite sum of positive quasi-characters. The source
then explicitly uses Section 2.5 to estimate the test Whittaker
function `W`. The resulting positive majorant (4.7.5) contains
both sets of growth exponents, and is integrated over the region

```text
1 ≤ |a₁| ≤ ⋯ ≤ |a_a|,     |a_(a+1)| ≤ ⋯ ≤ |a_r| ≤ 1
```

after harmless rescalings of the support bounds. Large positive `u`
provides decay in both directions. With the product of diagonal
absolute values fixed on each determinant slice, the source concludes
convergence for sufficiently large `u`.

The finite exponent sets come from the fixed full Whittaker-type
representations; coefficients, section values and Schwartz supports
affect the finite sums, constants and bounded cutoffs, rather than
requiring a new decay threshold. Thus the formal assertion uses one
bound before all sections, coefficient vectors, row Schwartz functions
and integers. The estimate of `W` involves the exponents of `π`;
the bound is consequently allowed to depend on `π`. Mere smoothness
does not supply this estimate. Evaluation on coefficient images
translates the source's Whittaker models to actual representations;
no equivalence requiring irreducibility is used.

## Boundaries

The imported data module proves integrability of each inner Fourier
integral, which does not establish this outer convergence. The compact
support argument on the different Section 4.6 quotient likewise does
not supply the Section 4.7 growth argument.

No global integrability over all determinant slices, Laurent-series
identity (4.7.1), Section 4.8 companion identity, Section 4.9 functional
equation or measure disintegration, induced Whittaker type, local-factor
existence, or gamma/L multiplicativity is asserted or assumed.
An independent proof of this proposition remains necessary.
