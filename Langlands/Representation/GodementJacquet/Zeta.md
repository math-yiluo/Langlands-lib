# Godement–Jacquet matrix integrals and JPSS Section 5.2 value modules

This module defines actual matrix integrals and the rational-value sets whose
Laurent spans are JPSS `I₂` and `I₃`. The namespace is
`Langlands.GodementJacquet`, with canonical p-adic specializations in its `Padic`
namespace. All actual ranks are `d = n + 1`, including rank one. The field and
representation carrier have independent arbitrary universes. Reducible
representations are retained; the definitions require no irreducibility,
admissibility, or finite generation.

## Source and correspondence

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions* (1983), Section 5.2, printed pages 420–421,
registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained source is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
one-based PDF pages 55–56 are printed pages 420–421. Both pages were read
visually. No source-specific registered erratum was located in the project
literature pointers or project/Library errata-note locations consulted.

On printed page 420, equation (2) defines

`Z(Φ,s,f) = ∫_{GL_d(F)} Φ(g) f(g) |det g|^s dg`,

where `Φ` is a Schwartz–Bruhat function on the full `d × d` matrix space
and `f` is a bi-K-finite matrix coefficient. Equation (3) uses the same
integral with `W` in the actual Whittaker model. The first paragraph on printed
page 421 defines `I₂` from `Z(Φ,s+(d-1)/2,f)` and `I₃` from
`Z(Φ,s+(d-1)/2,W)`, in the spectral variable `X = q^(-s)`.

The exact formal correspondence is:

- `biSmoothCoefficient σ ℓ v` uses the published `matrixCoefficient` and
  `smoothDualPairing`, so it is `g ↦ ℓ(σ(g)v)` for `ℓ : SmoothDual σ` and
  `v : smoothVectors σ`. `biSmoothMatrixCoefficients σ` is their complex
  linear span. This packages the source's smooth bi-K-finite coefficient
  space with both smoothness witnesses explicit, and remains defined when
  the whole algebraic representation is not smooth. No unrestricted dual or
  arbitrary-function replacement is used. The identification with the source's
  terminology is explanatory; this module proves no characterization theorem.
- `MatrixTestFunction n F` is `SchwartzBruhat` on
  `Matrix (Fin (n+1)) (Fin (n+1)) F`, including singular matrices.
  `matrixIntegrand abv Φ s f g` is exactly
  `Φ g.val * f g * determinantWeight abv g s`. Thus `matrixIntegral` has
  exponent **s**, as in printed page 420 equations (2),(3).
- `MatrixConverges` is `MeasureTheory.Integrable` for that integrand and the
  supplied measure. `matrixIntegral` is the totalized complex Bochner integral;
  its existence as a term supplies no convergence theorem.
- `jpssShift n = (n : ℂ)/2` is `(d-1)/2`. `ShiftedConvergesOnRight` requires
  integrability at `s + jpssShift n` on some right half-plane in **s**.
  `HasShiftedRationalValue q abv μ Φ f R` combines that witness with
  `HasRationalContinuation q (fun s => matrixIntegral abv μ Φ (s+n/2) f) R`.
  This continuation uses the published `spectralPoint q s = (q : ℂ)^(-s)`;
  the shift is in the integral exponent, not in the spectral-point argument.
- `matrixRationalValues` ranges over full-matrix test functions and actual
  members of `biSmoothMatrixCoefficients σ`. `whittakerRationalValues` ranges
  over full-matrix test functions and vectors of
  `glCoefficientModel ψ n σ ℓ`, for the specified standard Whittaker
  functional `ℓ : glFunctionals ψ n σ`. The evaluated function is the
  published `glModelFunction`. The set is defined even for a zero functional;
  later comparisons can require a nonzero functional and Whittaker type.
- `jpssI2` and `jpssI3` apply the existing `zetaSpan` to those respective
  rational-value sets. Their scalar ring is the actual `LaurentCoefficients`
  (`ℂ[X,X⁻¹]`) acting on `RationalFunctions` (`RatFunc ℂ`) through the
  published Laurent embedding. They are initially Laurent submodules.
  `jpssI2FractionalIdeal` and `jpssI3FractionalIdeal` use
  `fractionalZetaIdeal` only with an explicit `HasCommonDenominator` proof
  for exactly the corresponding value set.

## Measures and canonical p-adic specialization

The generic API exposes the absolute value, natural-number spectral base `q`,
and a measure on the Borel space of the actual general linear group.
Supplying a measure asserts no Haar existence or normalization, and the generic
absolute value need not be normalized. These parameters permit subsequent
comparisons with rank-one JPSS character zeta values using their existing
absolute-value, measure and spectral conventions. The generic spectral base has
no positivity restriction; applications use the canonical residue cardinality.

The `Padic` namespace specializes to every `F : PadicField p` with `p` prime.
Its section-local instances use `F.canonicalTopologicalData`: canonical field
topology, valuative relation and local-field structure, and the induced Borel
space on `GL_(n+1)(F)`. The wrappers `matrixIntegrand`, `MatrixConverges`,
`matrixIntegral`, `matrixRationalValues`, `whittakerRationalValues`, `jpssI2`
and `jpssI3` specialize the respective generic objects. They use
`normalizedAbsoluteValue F.canonicalTopologicalData`, whose normalization is
by the residue cardinality, and the existing `generalLinearHaar F.Carrier n`,
with the integral general linear subgroup of mass one. The rational-value
wrappers use exactly `F.canonicalTopologicalData.residueCardinality` for `q`.
No new Haar normalization or spectral norm is substituted.

## Internal packaging and scope

The convergence predicates, joint convergence/continuation membership relation,
value-set comprehensions, Laurent spans before fractional-ideal packaging, and
canonical wrappers are internal packaging of the displayed source formulas.
Requiring a convergence witness in each value avoids treating a totalized
nonintegrable integral as an analytic value. The convergence and continuation
half-planes may have different bounds; their intersection is again a right
half-plane. Defining these relations asserts no witness exists for arbitrary
input data.

The source's convergence, rationality and common-denominator assertions and its
subsequent comparisons require separate statement and proof tasks. This module
selects no rational continuation, normalized generator, L polynomial or gamma
factor. It asserts no convergence, rationality, bounded denominator,
`I₁ = I₂ = I₃`, product-ideal generation, functional equation or
multiplicativity theorem. The module contains definitions only.
