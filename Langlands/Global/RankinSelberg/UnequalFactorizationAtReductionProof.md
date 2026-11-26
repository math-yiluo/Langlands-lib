# Proof of the fieldwise unequal-rank integration step

Module `Langlands.Global.RankinSelberg.UnequalFactorizationAtReductionProof`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Result

`unequalArchimedeanFactorizationAtReduction :
UnequalArchimedeanFactorizationAtReductionStatement.{u, uQ}` proves the Library proposition
declared in [`UnequalFactorizationAtStatement`](UnequalFactorizationAtStatement.md). For every
number field `F` with compact `AdeleQuotient F`, `UnequalPointwiseFactorizationAt F` implies
`UnequalArchimedeanFactorizationAt F`. The pointwise premise is used only at the field `F`.
The universes `u` (field) and `uQ` (spectral presentation) are independent, as in the
statement. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Inputs from the Library

* `UnipotentClass.unipotentClassProductStatement` in
  [`UnipotentClassProductProof`](UnipotentClassProductProof.md) (the quotient-product
  identity B). For archimedean quotient measure data `DR`, `DC` and compatible quotient
  measures at the places of `S`, it gives a nonzero constant `C`. For all functions, the
  integral over `unipotentIntegralClasses F (t + 1) S` of a product of functions of the
  local classes equals `C` times the product of the local quotient integrals.
* `RectangleTate.rectangleTateStatement` in [`RectangleTateProof`](RectangleTateProof.md)
  (the rectangular Tate identity C). The global rectangular integral of a product of local
  functions, restricted to matrices integral outside `S`, is the product of the real,
  complex and `S` rectangular integrals, with constant `1`.
* `partialUnequalWhittakerIntegral_eq_setIntegral`, `partialDualWhittakerIntegral_eq_setIntegral`
  and `measurableSet_unipotentIntegralClasses` from `PartialIntegralExhaustion` express the
  global partial integrals as set integrals over the partial integral classes.
* `PadicUnequalTestData.isCompatible_quotientMeasure` from
  [`ArchimedeanFactorizationReduction`](ArchimedeanFactorizationReduction.md) supplies the
  compatibility needed to apply B.

## Proof

After introducing `F` with its instances and the pointwise premise at `F`, all the binders of
the integrated statement are introduced and passed to that premise. The premise yields
vectors `x`, `x'` spherical outside `S`, a constant `κ ≠ 0`, archimedean Whittaker
functions and quotient measure data, finite test data `D`, and local functions `fS`, `gS`.
These integrate to the ordinary and dual local integrals of `D`. The premise also gives the
pointwise identities for the integrand and the dual kernel on the partial integral classes
and the four nonvanishing clauses.

Apply B at `F` with `DR`, `DC` and the quotient measures of the test data. This gives
`C ≠ 0`. The integrated statement is then witnessed by the same vectors, Whittaker functions,
measure data and test data, with constant `C κ` (nonzero as a product of nonzero numbers)
and half-plane bound `σ = 0`. The four nonvanishing clauses are those of the premise. Both
identities hold for every `s`, so the half-plane hypothesis is not used.

* **Ordinary integral.** Write the partial integral as a set integral over the classes and
  replace the integrand by the pointwise factorization on that set. Take `κ` out, apply B,
  rewrite each finite factor by the integral of `fS`, unfold the real and complex local
  integrals, and finish with `ring`.
* **Dual integral.** On each class `q`, the dual integrand is the integral of the dual kernel
  over the rectangular matrices. The pointwise identity, which holds for every matrix, gives
  `κ` times the indicator of integrality outside `S` applied to a product of local kernels.
  C turns its integral into the product of the real, complex and finite rectangular
  integrals at `q`. The resulting function of `q` is a product of functions of the local
  classes. B then gives `C` times the product of the local quotient integrals of these
  rectangular integrals. The finite ones are the dual integrals of `D` by the identity for
  `gS`, and the archimedean ones are the real and complex dual integrals after unfolding
  `blockIntegral` and the dual kernels. `ring` finishes.

This is the integration argument of `unequalArchimedeanFactorizationReduction`, which uses
the global premises A_U, B and C. Here the pointwise premise is a hypothesis at the single
field `F`, and B and C are the published theorems, applied at `F`.

## Provenance

This is an internal proof of a derived Library interface. The integrated proposition
formalizes the unequal-rank product step in J. W. Cogdell, *Analytic theory of
L-functions for GL_n*, in J. Bernstein and S. Gelbart (eds.), *An Introduction to the
Langlands Program*, Birkhäuser, 2004, pp. 197–228, registered as
`cogdell-2004-analytic-theory-gln`: proof of Theorem 4.1, printed pp. 219–220 (PDF
pp. 222–223), where for suitable vectors the global integral is the product of the local
integrals at the places of `S` and the partial L-function. Cogdell's §2.3, printed p. 210
(PDF p. 213), decomposes the equal-rank integral over `N_n(𝔸) \ GL_n(𝔸)` of a product of
local functions into a product of local integrals, because the domain of integration
factors. In this proof that step is the quotient-product identity B, and the additional
integration over rectangular matrices in the dual integral is the rectangular Tate
identity C. The fieldwise split and the pointwise premise are Library interfaces, not
assertions attributed to Cogdell, so this proof does not follow a source argument line by
line. It does not prove the pointwise premise.
