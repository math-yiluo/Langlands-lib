# A conditional reduction of equal-rank and full archimedean factorization

Module `Langlands.Global.RankinSelberg.EqualArchimedeanFactorizationReduction`,
namespace `Langlands.Global.RankinSelbergGlobal`. The module imports the shared
measure interfaces and the unequal-rank reduction in `ArchimedeanFactorizationReduction`.

This is an internal conditional result. It does not prove
`ArchimedeanFactorizationStatement`. Its entry proposition is
`ArchimedeanPointwiseFactorizationReductionStatement.{u,uQ}` and is proved by
`archimedeanPointwiseFactorizationReduction`. Both universe parameters are free.

## The normalized finite quotient measure

For a p-adic field `K` with its canonical topology,
`equalPadicQuotientMeasure K r` is the Library's
`unipotentQuotientHaar K.Carrier r`, with the Borel measurable structure on
`LeftUnipotentQuotient r K.Carrier`. This is the quotient measure used by
`EqualLocalTestData.integral` and `EqualLocalTestData.dualIntegral`.

`equalPadicQuotientMeasure_isCompatible` proves the condition
`IsCompatiblePadicQuotientMeasure`: the unipotent Haar measure is right invariant
and the quotient measure satisfies the compatibility condition with the ambient
and subgroup Haar measures. Right invariance comes from the existing instances;
compatibility is the published theorem `unipotentQuotientHaar_isCompatible`.
The declarations introduce no measure-normalization assumption.

## The pointwise equal-rank premise

`EqualPointwiseFactorizationAt F` is the pointwise statement for the specified number
field `F`. Its universal closure `EqualPointwiseFactorizationStatement.{u,uQ}`, called
A_E here, has the same universal binders as
`EqualArchimedeanFactorizationStatement.{u,uQ}`. In particular it allows every
number field `F : Type u` with compact `AdeleQuotient F`, an additive character
trivial on `F`, every rank `r`, the supplied cuspidal realizations and
contragredients, spectral presentations in universe `uQ` with irreducible
admissible components, and the prescribed finite set, additive components,
self-dual finite measures and archimedean parameters. There is no positive-rank
restriction: `r = 0`, the GL1 case, is included.

Under these binders A_E retains the choices of the target: vectors `x`, `x'`
spherical outside `S`, a function `Φ` in `schwartzBruhat F (r + 1)` standard
outside `S`, archimedean Whittaker restrictions `WR`, `WR'`, `WC`, `WC'`,
archimedean Schwartz functions `ΦR`, `ΦC`, quotient measure data `DR`, `DC`,
and local data `D v : EqualLocalTestData` for `v : S`. It retains both exact
pointwise formulas from the target: the factorization of `Φ` into these local
Schwartz factors, and the factorization of its global Fourier transform into
their local Fourier transforms, in each case with scalar exactly one.

It replaces the two global integral identities by the following data and
pointwise requirements. There is one nonzero complex scalar `κ` and, at each
`v : S`, families of functions `fS v s`, `gS v s` on the local quotient such that:

1. Integration of `fS v s` against `equalPadicQuotientMeasure` is
   `(D v).integral s`, and integration of `gS v s` is `(D v).dualIntegral s`,
   for every complex `s`.
2. For every `s` and every class `q ∈ unipotentIntegralClasses F (r + 1) S`,
   `equalWhittakerIntegrand F W W' Φ s q` is `κ` times the product of the
   archimedean `realEqualIntegrand` and `complexEqualIntegrand` values and the
   `fS v s` values at the local classes of `q`. Here `W` and `W'` are the global
   cusp Whittaker functions of `x` and `x'`.
3. On the same set of classes, for every `s`, the corresponding integrand for
   `dualFunction W`, `dualFunction W'` and the global Fourier transform of `Φ`
   is the same `κ` times the product of the archimedean equal integrands for
   the local dual Whittaker functions and the local Fourier transforms, and
   the values of `gS v s` at the finite classes.

The local classes are the definitions `realQuotientProjection`,
`complexQuotientProjection` and `finiteQuotientProjection` from the imported
module. The ordinary archimedean factors are explicitly
`realEqualIntegrand (WR v) (WR' v) (ΦR v) s` and its complex analogue. The dual
ones replace each Whittaker function by `ArchimedeanLocal.dualFunction` and
each Schwartz function by the corresponding `realFourierTransform` or
`complexFourierTransform` for `aR v` or `aC w`.

Finally A_E retains the four nonvanishing conclusions of the target, with the
same quantifiers: for every real `a` there is a complex `s` with `a < s.re`
where the ordinary archimedean product, respectively the dual archimedean
product, is nonzero; and the analogous assertions for each local integral and
dual integral of `D v` at every `v : S`.

A_E is an open premise. Neither Fourier factorization nor these nonvanishing
assertions are proved by this module. The separately developed Schwartz tensor
assembly gives a construction for the ordinary Schwartz membership and product
formula, but is not used in this reduction; those clauses remain explicit here.

## Equal-rank integration

The other premise is the imported statement
`UnipotentClassProductStatement.{u}`, called B, which the Library proves as
`UnipotentClass.unipotentClassProductStatement` (module
`UnipotentClassProductProof`): for fixed archimedean quotient
measures and compatible finite quotient measures at `S`, one nonzero scalar
`C` relates integration over `unipotentIntegralClasses F (r + 1) S` to the
product of the corresponding local quotient integrals, for every family of
local functions. Its exact hypotheses and its measure comparison are
documented in the paired Markdown of the imported module.

The proposition `EqualArchimedeanFactorizationReductionStatement.{u,uQ}` is

```text
EqualPointwiseFactorizationStatement → UnipotentClassProductStatement →
  EqualArchimedeanFactorizationStatement.
```

`equalArchimedeanFactorizationAt_of_pointwise` uses the pointwise hypothesis at `F` and
applies the quotient-product measure formula for that field. Quantification over `F` gives
`equalArchimedeanFactorizationReduction`. The integration argument applies B to `DR`, `DC`
and the normalized finite quotient measures, whose compatibility has already
been proved, obtaining `C ≠ 0` and the product integration formula. It chooses
`c = C * κ`, nonzero by `mul_ne_zero`, and `σ = 0`.

For each integral identity, the published
`partialEqualWhittakerIntegral_eq_setIntegral` rewrites the partial global
integral as an integral over the measurable set of integral classes.
`setIntegral_congr_fun` substitutes the corresponding pointwise formula of A_E
on that set. `integral_const_mul` extracts `κ`. The single product integration
formula from B applies to the ordinary local integrands, respectively the dual
local integrands. The defining identities for `fS` and `gS` identify the finite
local integrals; unfolding the archimedean equal-integral definitions identifies
the remaining factors. Commutativity and associativity of complex
multiplication give `c` times the required archimedean and finite products.

The same `C` applies in both calculations because B supplies it before the
choice of local functions; A_E supplies the same `κ` for both pointwise
identities. Thus the resulting `c` is exactly the same for the ordinary and
dual integrals. The identities are proved for every `s`, which implies the
target's required identities for `0 < s.re`. No convergence premise is added.
All other conclusions of the target come directly from A_E.

## Both ranks and retained obligations

The entry proposition `ArchimedeanPointwiseFactorizationReductionStatement`
is the implication

```text
UnequalPointwiseFactorizationStatement → EqualPointwiseFactorizationStatement →
  UnipotentClassProductStatement → RectangleTateStatement →
    ArchimedeanFactorizationStatement.
```

Its proof combines the imported `unequalArchimedeanFactorizationReduction`
with `equalArchimedeanFactorizationReduction` and forms the conjunction that
defines the full target. `RectangleTateStatement` is used by the unequal-rank
reduction for its inner rectangular integral; it is not needed for the
equal-rank integration step.

Of the four named premises, A_U and A_E remain open; B and C are proved in
the Library (modules `UnipotentClassProductProof` and `RectangleTateProof`).
A_U is the imported unequal-rank
representation-theoretic pointwise premise; A_E includes the equal-rank
representation theory, exact Fourier formula and nonvanishing; B is the
quotient-product measure comparison; C is `RectangleTateStatement`, the
self-dual additive measure product comparison. Proving this conditional
implication does not discharge any of those premises or give an
unconditional proof of `ArchimedeanFactorizationStatement`.

This decomposition is internal implementation infrastructure. It is derived
from the two published target definitions and the imported explicit premises,
rather than asserted as a new translation of a source theorem. The proof is
integration and propositional composition, and introduces no new axioms.
