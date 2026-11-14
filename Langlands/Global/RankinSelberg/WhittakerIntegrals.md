# Global Whittaker integrals for unequal ranks

This file defines the ordinary and dual global Whittaker integrals of
Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2,
printed pp.206–207 (PDF pp.209–210), registered as
`cogdell-2004-analytic-theory-gln`. These are definitions; convergence,
unfolding, and factorization are separate assertions.

Write `n = r + 1`, `m = t + 1`, with `t < r`. The number field has
arbitrary universe `u`. `Points F j` is the Library's actual adelic
`GL_j` carrier, as in `UnequalIntegrals`. The functions accepted here are
ordinary complex-valued functions on those carriers. In the unfolding
statement they will be the Library's actual global Whittaker coefficients
of actual cuspidal vectors.

## Quotient and measure

`unipotentAdelic F m` is the adelic point subgroup of the existing upper
unitriangular subgroup functor. `WhittakerQuotient F m` is the actual
left homogeneous space `N_m(𝔸) \ GL_m(𝔸)` with its quotient topology
and measurable structure. The Borel-space instance reuses the Library's
quotient Borel theorem.

`unipotentRationalImage` is the image of actual rational unipotent points
in the ambient adelic group. Its inclusion in the ambient principal
subgroup and its discreteness are proved in this file.
`toWhittakerQuotient` is the natural map

`N_m(F) \ GL_m(𝔸) → N_m(𝔸) \ GL_m(𝔸)`.

The file proves that this map is continuous and measurable, using the
Library's Borel structure on a discrete-subgroup quotient.
`whittakerQuotientMeasure` is explicitly the pushforward under this map
of `LeftCosetSpace.haarQuotientMeasure` for the discrete rational
unipotent image. That source measure uses the fixed ambient
`Measure.haar` on `GL_m(𝔸)` and counting measure on `N_m(F)`.
Thus this construction fixes the quotient normalization by first
quotienting by counting measure and then integrating out the compact
fiber `N_m(F) \ N_m(𝔸)` with mass one. In the usual quotient notation
it is `dg/dn`, where `dn` has rational covolume one. No probability
normalization is imposed on `N_m(𝔸) \ GL_m(𝔸)`.
The code defines this pushforward directly; it does not add a general
transitivity-of-quotient-integration theorem.

`rectangleMeasure F k m` is a measure on the actual matrix space
`M_(k,m)(𝔸)`, equipped with its Borel structure. It transports
`GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure` by the
continuous two-block coordinate homeomorphism, followed by `toAdd`.
The measurability of this map is proved here. This reuses the existing
intrinsic unipotent Haar normalization, scaled by the mass of its
rational quotient. With the standing compactness hypothesis on
`AdeleQuotient F`, that quotient has mass one; the comparison and
counting-measure Weil formula are already supplied by
`GeneralLinearBlockIntrinsicMeasure`. Hence the rectangular additive
measure has rational covolume one. Its definition remains an explicit
mass-scaled pushforward without inserting compactness as data.

## Matrices, powers, and integrals

The padding and determinant-power conventions are those of
`UnequalIntegrals`: the determinant is the Library's normalized idelic
absolute value and a complex power means
`exp(z * log |det g|)` with the real logarithm.
The ordinary integrand is

`W(diag(g,I_(n-m))) W'(g) |det g|^(s-(n-m)/2)`.

`unequalWhittakerIntegral` integrates this over `WhittakerQuotient F m`
against `whittakerQuotientMeasure F m`, giving Cogdell's
`Ψ(s;W,W')` on p.206.

`rectangularPoint` uses the existing actual lower-block localization
matrix and rank reindexing to construct

```text
[ g          0        0 ]
[ x     I_(n-m-1)     0 ]
[ 0          0        1 ].
```

Here `x ∈ M_(n-m-1,m)(𝔸)`. The identity block is allowed to have size
zero. `dualWhittakerKernel` replaces the padded argument of `W` by
this matrix and keeps the same factors `W'(g)` and
`|det g|^(s-(n-m)/2)`.
`dualWhittakerIntegrand` first integrates the kernel in `x` against
`rectangleMeasure`; `dualWhittakerIntegral` then integrates in `g`
against the Whittaker quotient measure. This is exactly the iterated
defining integral `Ψ̃(s;W,W')` displayed on p.207.

`unfoldingWeyl` is `diag(I_m,w_(n-m))`, with the existing antidiagonal
long Weyl matrix. `translateFunction n a W` means positive right
translation, `g ↦ W(g a)`. Neither operation is hidden in the dual
integral: its first function is supplied explicitly. In the dual
unfolding it is `translateFunction n (unfoldingWeyl F h) W̃`, where
`W̃(g)=W(w_n ᵗg⁻¹)` uses the existing `dualFunction` convention.

## Representatives and convergence

The quotient integrands use `q.out`, just as the existing global
integrals do. For arbitrary input functions this specifies a
representative-dependent definition. For Whittaker functions with
opposite characters the ordinary product descends; for the dual
integral the inner rectangular integration gives the required
descent after a change of variables. These descent and unfolding
claims are not proved by the definitions.

All displayed integrals are totalized Bochner integrals, with value
zero when the relevant function is not integrable. In particular,
the definitions do not assert absolute convergence or supply
continuations outside convergence regions. Absolute convergence of
the dual integral must include convergence of the inner integrals
and integrability of their absolute integrals; integrability of the
totalized outer integrand alone would not express that claim.
