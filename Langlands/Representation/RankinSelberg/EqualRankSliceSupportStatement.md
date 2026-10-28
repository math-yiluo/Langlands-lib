# Equal-rank determinant-slice lower support

Worker 488 states
`Langlands.RankinSelberg.EqualRankSliceSupportStatement.{uF,uV,uW}`
in `Langlands.Representation.RankinSelberg.EqualRankSliceSupportStatement`.
Worker 484 proposed the focused support interface and its internal proof route.
The telescope uses Worker 11's published analytic interfaces.
This module defines a proposition and does not prove it.

## Complete statement

The parameters are an arbitrary `p : ℕ` with `[Fact p.Prime]`,
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and `n : ℕ`.
The actual group has rank `n + 1`, so `n = 0` is `GL₁`.
The statement installs `T.topology`, `T.valuativeRel` and `T.localField`,
then the Borel measurable structures and corresponding `BorelSpace`
instances on the actual general linear group, upper-unipotent subgroup,
and `LeftUnipotentQuotient n F.Carrier`, in exactly the order used by
`EqualRankAnalyticStatement`. In particular the quotient's Borel structure
is induced by the supplied topology, as required by
`equalRankSliceCoefficient`; no unrelated measurable structure is quantified.

After these local instances the proposition quantifies, in order:

1. Every `ψ : UnitaryAdditiveCharacter F.Carrier`. This structure already
   contains continuity, unit-circle values and nontriviality.
2. Every instance of
   `Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)`.
3. Every quotient measure `μ` on the specified Borel structure, subject to
   the existing
   `QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F.Carrier)
   (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ`.
   Thus the Haar measures and their quotient normalization are the same as
   in the analytic statement; no existence assertion is substituted for
   the supplied compatible measure.
4. Independent carriers `V : Type uV` and `W : Type uW`, each with
   `AddCommGroup` and `Module ℂ` instances, and actual representations `π`
   and `σ` of `Langlands.GeneralLinear (n + 1) F.Carrier` on these carriers.
5. Exactly the hypotheses
   `IsOfWhittakerType n (standardCharacter ψ n) π` and
   `IsOfWhittakerType n (inverseStandardCharacter ψ n) σ`.
   Each means admissibility (including smoothness), finite generation over
   the actual group algebra, and a linear equivalence between the full
   indicated equivariant-functional space and `ℂ`. Finite generation here
   is not finite dimensionality of the carrier over `ℂ`.
6. Every actual `ℓ : glFunctionals ψ n π` and
   `ℓ' : glInverseFunctionals ψ n σ`, every
   `f : (coefficientModel π ℓ).toSubmodule` and
   `f' : (coefficientModel σ ℓ').toSubmodule`, and every
   `Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)`.

The conclusion is exactly

```text
Langlands.HarmonicAnalysis.BilateralLaurentSeries.HasLowerBoundedSupport
  (equalRankSliceCoefficient T μ ψ f.val f'.val Φ).
```

The imported series type is the space of functions `ℤ → ℂ`. Its published
`BilateralLaurentSeries.hasLowerBoundedSupport_iff` identifies this conclusion
with

```text
∃ M : ℤ, ∀ m : ℤ, m < M →
  equalRankSliceCoefficient T μ ψ f.val f'.val Φ m = 0.
```

The bound is chosen after all the listed data, including the coefficients
and test function. No uniformity over all coefficients or tests is claimed.
The field and two carrier universes remain independent.

## Source correspondence and scope

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, source `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.385–386, 388–391 and 406–407 were read visually for this statement.
No source-specific erratum file was found in the supplied Library,
workspace or project `notes/errata` locations on 27 October 2026.

In §4.2, (4.2.1), p.406, the source uses
`G_r^m = {g : |det g| = q^(-m)}` and defines
`Ψ^m(W,W';Φ) = ∫_{N_r \ G_r^m} W(g) W'(g) Φ(η_r g) dg`.
Here `r = n + 1`, `η_r g` is the last row, and
`q = T.residueCardinality`. The imported determinant slice is the fiber
`T.ord (det g) = m`; the published
`mk_mem_determinantSlice_iff_normalizedAbs` proves that it is the source
condition. The imported coefficient is the restricted integral of the
existing equal-rank integrand at spectral parameter zero, whose representative
value is `f.val.val g * f'.val.val g * Φ(lastRow g)`.

Page 407 first uses convergence and Fubini to obtain the expansion (4.2.2),
and then explains why its coefficients vanish for sufficiently negative
integer indices. The latter assertion is the endpoint stated here.
The source's torus reduction (2.7.3), p.391, and its version (4.2.3),
p.407, combine bounded simple-root coordinates with bounded last-diagonal
coordinate from the test function to bound `|det g|` above. With the
normalization `|det g| = q^(-m)` and `q > 1`, an upper determinant bound
corresponds to a lower bound on `m`.

JPSS §2.1, pp.385–386, defines Whittaker type using admissibility, finite
type and a one-dimensional functional space, and realizes its Whittaker
functions as `g ↦ ℓ(π(g)v)`. Theorem 2.7, pp.390–391, has this full-type
scope. The present target likewise permits reducible representations.
It additionally retains zero choices of the functional and coefficient:
the corresponding integrand and every slice coefficient are zero.
No nonzero-functional hypotheses are needed for the support endpoint.
Rank one is included with its actual group and test-function space.

The full-type formulation is supported by an internal route that avoids
assuming a single-gauge bound. JPSS §2.5, p.388, imposes a unitary central
character in its single-gauge majorization and gives its displayed finite
torus expansion in the generic setting. Those stronger estimates are not
premises of this proposition, nor is their unrestricted scope attributed
to the source.

The published theorem `Langlands.Whittaker.smoothSimpleRootSupport` in
`Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof` proves the
corresponding support target for arbitrary smooth coefficient images.
For each coefficient it gives a positive upper bound for every adjacent
diagonal ratio, uniformly over the integral Iwasawa factor. Smoothness is
available here from the admissibility part of `IsOfWhittakerType`.
Unipotent equivariance alone does not make an arbitrary element of
`WhittakerFunctions` smooth; this statement therefore quantifies actual
coefficient images, not all algebraically equivariant functions.

A prospective proof can apply that theorem to the first coefficient,
use actual Iwasawa decomposition, and combine compact support of
`Φ(lastRow g)` with the integral factor to bound the last diagonal entry
where the integrand is nonzero. The adjacent-ratio bounds then bound
every diagonal entry and hence the normalized determinant. Sufficiently
negative determinant slices have identically zero integrand, so their
integrals vanish. For `n = 0` there are no adjacent ratios; compact test
support bounds the single diagonal entry directly. These geometric and
integration steps remain proof obligations of a separate successor.

## Boundary of this unit

The coefficient uses the existing total Bochner integral. The statement
assumes neither slice integrability nor convergence, and asserts neither.
It adds no irreducibility, unitary central character, gauge estimate,
asymptotic expansion, or lower-support premise. It does not prove a Laurent
expansion, half-plane convergence, rational continuation, or any gamma,
epsilon or L-factor claim. The determinant-slice, bilateral-series and
analytic statement pairs are imported without changes.
