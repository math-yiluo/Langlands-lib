# Torus Mellin integrals in diagonal coordinates

Module `Langlands.Representation.GodementJacquet.WhittakerTorusMellin`,
namespace `Langlands.GodementJacquet.WhittakerTorus.Padic`.

Let `F` be a p-adic field with its canonical topological data (topology,
valuation, local field structure). `Fˣ` carries the Borel σ-algebra, and the
torus `(Fˣ)^(n+1)` carries the product `da` of the normalized multiplicative
Haar measures `localMultiplicativeHaar`. Write `|·|` for the normalized
absolute value and `q` for the residue cardinality. Assume
`FiniteFunctionMellinStatement`. The module proves the following. Let `η` be a
finite function on `(Fˣ)^(n+1)`, `φ` a Schwartz–Bruhat function on `F^n` and
`J` a Schwartz–Bruhat function on `F^(n+1)`. Then the integral

`∫ φ(a_0/a_1, …, a_(n-1)/a_n) · J(a_0, …, a_n) · η(a) · |a_0 ⋯ a_n|^s da`

converges absolutely for `Re s` large. It also has a rational continuation
in `q^(-s)` (`HasRationalContinuation`).

## Source and provenance

The content is internal and derived. It is one step in reducing
`ModelWhittakerRationalityStatement` (convergence and rationality of every
full-matrix Whittaker integral on the coefficient model) to
`FiniteFunctionMellinStatement` and the torus expansion of Whittaker
functions. After the Iwasawa decomposition and the torus expansion, each
Whittaker integral is a finite linear combination of integrals of exactly this
shape. Here `J` is the Schwartz–Bruhat slice integral of the test function
(module `WhittakerSliceSchwartz`), `φ` is a coefficient test function of the
expansion, and `η` collects the expansion's finite function, the modulus
character and a power of `|det|`. The finite-function Mellin statement is a
proposition target taken from Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), printed page 392,
displays (5)–(6). This module only changes variables so that statement
applies.

The change of variables is the standard one. The same paper, printed page 391,
equation (4), writes the torus element as
`a = diag(a_1 a_2 ⋯ a_r, a_2 ⋯ a_r, …, a_r)`, which is `a = τ(x)` with the
indices shifted by one. Printed page 392 uses these coordinates to obtain the
weight `|a_1 a_2^2 ⋯ a_r^r|^s` and the products (6). Jacquet,
Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3) I*, Ann. of Math.
109 (1979), printed page 183, equation (2.3.2), use the same coordinates for
gauges. What is internal here is the Lean packaging (one finite function `η`
on the whole torus, the explicit transfer of integrability and of the integral
along `τ`) and the case of the test function: in the 1983 proof on printed
pages 391–392 the Schwartz–Bruhat factor is `Φ(a_r)`, a function of the last
coordinate only, while here `J` is a Schwartz–Bruhat function of all diagonal
entries, as for the full-matrix integrals. The Schwartz–Bruhat property of
`initTail φ J` in that case is `initTail_mem`; see the paired Markdown of
`WhittakerTorusCoordinates`.

## Declarations

- `ratios a`: the adjacent ratios `a_i / a_(i+1)` (`i < n`) of a torus element
  `a`, as elements of `F`.
- `torusIntegrand φ J η s a`: the integrand
  `φ(ratios a) · J(a) · η(a) · |∏_i a_i|^s`, where `J` is evaluated at the
  values of the units `a_i` in `F`.
- `initTail φ J`: the Schwartz–Bruhat function `y ↦ φ(y_0, …, y_(n-1)) · J(τ(y))`
  on `F^(n+1)`. Here `τ(y)_j = ∏_{k ≥ j} y_k` is the tail product. It is a
  Schwartz–Bruhat function by `initTail_mem` of `WhittakerTorusCoordinates`.
- `torusIntegrand_tailProd`: in tail-product coordinates `a = τ(x)` the
  integrand is

  `initTail φ J (x) · η(τ(x)) · ∏_i |x_i|^((i+1) s)`.

  Proof: `ratios (τ x) = (x_0, …, x_(n-1))` (`tailProd_div_tailProd`). The
  values of the units `τ(x)_j` are the tail products of the values of the
  `x_k` (`coe_tailProd_units`). The determinant weight is rewritten by
  `cpow_abv_prod_tailProd`.
- `torusMellin`: the main theorem. Under `FiniteFunctionMellinStatement`:
  1. there is `c` such that `torusIntegrand φ J η s` is integrable for
     `da` whenever `c < Re s`;
  2. there is a rational function `R` such that `s ↦ ∫ torusIntegrand φ J η s da`
     has rational continuation `R` in `q^(-s)`.

  Proof: apply `FiniteFunctionMellinStatement` to the canonical topological
  data of `F`, with `r = n + 1`, weights `m i = i + 1` and the one-element
  family `{η ∘ τ}`. The function `η ∘ τ` is finite by
  `IsFiniteFunction.comp`, because `τ` is a continuous group automorphism of
  the torus. The statement's integrand for `η ∘ τ` and the Schwartz–Bruhat
  function `initTail φ J` is `torusIntegrand φ J η s ∘ τ`
  (`torusIntegrand_tailProd`). `τ` preserves `da`
  (`measurePreserving_tailProd`) and is a measurable embedding (it is a
  homeomorphism). Hence integrability and the integral transfer from the
  pulled-back integrand to `torusIntegrand` through
  `MeasurePreserving.integrable_comp_emb` and
  `MeasurePreserving.integral_comp`. Second countability of `F`
  (`PadicField.TopologicalData.secondCountableTopology`) and of `Fˣ` (through
  the embedding of units) is needed by `measurePreserving_tailProd`.

The theorem does not use the common-denominator part of
`FiniteFunctionMellinStatement`.

`torusMellin` keeps `FiniteFunctionMellinStatement` as an explicit hypothesis
and this module does not import its proof. The Library proves the statement as
`Langlands.RankinSelberg.finiteFunctionMellin` (module
`Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof`), so
downstream users can supply it.
