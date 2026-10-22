# Archimedean abelian local analysis

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Archimedean.Statement`.
It is moved from `Langlands.LocalFactor.ArchimedeanStatement` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
The [migration record](../Abelian/Definitions.md#structural-migration-record) gives the complete map and checks.


Worker 33 authored this theorem-statement family for task
`722e8992-bab8-4859-abf9-98fa81f4cd4f`, revision 1. Its closing declaration is
`Langlands.LocalFactor.ArchimedeanAbelianLocalAnalysisStatement`. These are
proposition definitions, not proofs or assumed axioms.

## Actual objects and conventions

All underlying objects come directly from the pinned Mathlib: real and complex
numbers, `ContinuousMonoidHom` on their unit groups, `SchwartzMap`, Lebesgue
measure, the Bochner integral, `Complex.Gammaℝ`, `Complex.Gammaℂ`, and
`MeromorphicNFOn`. There are no project definition dependencies or arbitrary
local-factor symbols. Concrete integrands and predicates are local `let`
expressions in the propositions, not a rival global definition framework.

The real absolute value is the usual one. The complex arithmetic absolute
value is the square of the Euclidean norm. The Fourier kernels are respectively
`exp(2*pi*i*a*x*y)` and `exp(4*pi*i*Re(a*x*y))`. Thus both use the plus sign,
and the complex kernel uses the trace from C to R. The basic measures are
Lebesgue measure on R and twice Euclidean area on C.

`ArchimedeanQuasicharactersStatement` classifies all continuous complex
quasicharacters of the actual unit groups uniquely as
`sign(x)^e * |x|^t`, with `e` in `{0,1}`, and
`(z/||z||)^m * ||z||^(2*t)`, with integral `m`. The exponent `t` is complex.
No unitarity assumption is added.

The two Fourier components assert convergence, Schwartz closure, inversion,
inversion using the inverse additive character, and uniqueness among regular
additive Haar measures. Their explicit self-dual measures are
`sqrt(|a|) dx` and `2*||a|| dx dy`. They also state positive scalar Haar
scaling and additive-character dilation. Self-duality is a conclusion;
Fourier inversion is not a hypothesis of its own statement.

For fixed Haar measure `c` times the basic measure, the unique dual measure
is explicitly `|a|/c` times the basic real measure and `||a||^2/c` times the
basic complex measure. Composing the Fourier integral with its inverse-character
integral using these two measures recovers the original Schwartz function.
The self-dual measure is the positive square root of this product constraint.

## Continuation and separate L/epsilon normalization

The zeta integrals use `dx/|x|` and `2 dx dy/||z||^2` through explicit
additive-measure integrands. The single point zero is assigned integrand zero.
Absolute convergence is asserted when `Re(s+t)>0`.

Each Schwartz function has a unique meromorphic continuation in Mathlib's
normal form, agreeing with its zeta integral on that half-plane. Normal form
uses the analytic value at removable singularities and the representation
value zero at genuine poles. The latter is not declared to be a finite
analytic value. All functional equations are explicitly equalities of
punctured germs at every complex point. Thus cancellations or poles do not
produce false pointwise identities.

The L factors are separately normalized as
`Gammaℝ(s+t+e)` and `Gammaℂ(s+t+|m|/2)` by Gaussian zeta integrals.
Here Mathlib's `Gammaℂ(u)` includes its factor 2. The complex Gaussian is
`conj(z)^m exp(-2*pi*||z||^2)/pi` for nonnegative m and
`z^|m| exp(-2*pi*||z||^2)/pi` for negative m. The division by pi is essential:
Tate's unscaled Gaussian gives pi times this Gamma factor.

For the basic additive characters and measures, the epsilon constants are
`i^e` and `i^|m|`. For additive character scaled by `a` and fixed Haar measure
scaled by positive `c`, the multipliers in the spectral variable are

- real: `c * sign(a)^e * |a|^(s+t-1) * i^e`;
- complex: `c * (a/||a||)^m * ||a||^(2*(s+t-1)) * i^|m|`.

The functional equations use the actual Fourier transform, with dual
parameters `(e,-t)` and `(-m,-t)` at `1-s`. The displayed exponent `s-1`
belongs to fixed Haar measure. Substituting the self-dual Haar scale from
the Fourier components changes it to the familiar `s-1/2`. Thus the two
measure conventions and the half shift remain distinct.

## Original-source correspondence

- `tate-1967-thesis`, SHA256
  `01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`:
  J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*,
  in Cassels--Fröhlich, *Algebraic Number Theory* (1967), Chapter XV.
  Section 2.2, Theorem 2.2.2 and its measure discussion, printed pp.308--311
  (retained PDF spreads 163--164); section 2.3, Theorem 2.3.1 and character
  classification, pp.311--313 (spreads 164--165); section 2.4, Lemmas
  2.4.1--2.4.3 and Theorem 2.4.1, pp.313--316 (spreads 165--167);
  section 2.5, real and complex Gaussian computations, pp.316--319
  (spreads 167--168). These original scanned pages were read visually.
  Tate writes his basic additive map as minus the trace, then puts a minus
  sign in his Fourier kernel. The resulting archimedean kernel is the plus
  kernel used here.
- `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
  *Number theoretic background*, sections 3.1--3.2, printed pp.12--13
  (retained Corvallis Part II PDF pp.21--22), especially (3.2.1)--(3.2.5)
  for the local equation, measure/character scaling, and archimedean
  epsilon constants.
- `deligne-1973-local-constants`, SHA256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  *Les constantes des équations fonctionnelles des fonctions L*, section 3,
  internal/PDF pp.26--28 (journal pp.526--528), for the Gamma normalizations,
  rank-one equation and archimedean epsilon constants.

This is a derived formulation of the original results. It specializes Tate's
test class to actual Schwartz functions, expresses meromorphic continuation
by its canonical normal representative, and combines the basic functional
equation with character/measure scaling. No additional analyticity theorem
is silently postulated in the hypotheses.

The pinned environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1.

## Scope and validation status

This contribution covers archimedean abelian local analysis. It does not define
the real Weil group, classify its two-dimensional representations, assert
archimedean nonabelian induction, or prove global functional equations. Those
require the respective genuine objects and remain outside this contribution.
The broad parent task also retains its separate nonarchimedean, nonabelian,
ramification, stability, and WD obligations.

Whole-target check `4e4cd86d-9b65-4727-9f15-879179f86471` compiled the
module and inspected the closing proposition successfully, with no errors
or warnings. It returned `statement_returns_prop = true`, no free universe
parameters (the archimedean fields are concrete), and target fingerprint
`dacc90e9f84bfdc175830bb4f55f7dfaacdceb8dc90b2b5a1bb48e644a292328`.
The inspected axiom closure contains only `propext`, `Classical.choice`,
and `Quot.sound`. This validates elaboration, not the truth of the proposed
theorems. Independent semantic review and publication are required.
