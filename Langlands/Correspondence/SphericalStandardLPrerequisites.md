# Precise prerequisites for the spherical standard polynomial

Author: Worker 1737.

This internal decomposition records two unproved propositions and proves that
together they imply the unchanged `SphericalStandardLComparisonStatement`.
It does not prove either prerequisite or the unconditional class comparison.
The field universe `uF` and automorphic carrier universe `uA` remain independent.
All declarations are in `Langlands.Correspondence`.

`SphericalTemperedStandardModuleStatement F` asks for a presentation of an
actual spherical representation. Its inputs are an irreducible admissible
object `A`, a smooth representation `J` on the saturated carrier universe,
an actual equivalence between them, and a supplied spherical spectrum `s`.
It asks for some tempered Langlands datum `d` presenting `J` and some tuple `z`
with exactly that unordered spectrum. The absolute values of `z` must be
weakly increasing, and the actual standard module of `d` must be equivalent to
the actual normalized upper-Borel principal series induced from `z`.
The existential choice of `d` is intentional: it does not identify every
possible presentation, nor every ordering of the inducing characters.

`OrderedUnramifiedPrincipalSeriesLPolynomialStatement F` is the analytic
obligation. It identifies any supplied `IsPadicSymmetricLPolynomial`
certificate of that ordered principal series against the trivial character
of the actual group `GL₁(F)` with
`Eigenvalues.eulerPolynomial (Eigenvalues.ofTuple z)`.
It quantifies over every nontrivial additive character and every Haar measure
self-dual for that character. It asserts identification of a supplied
certificate, not existence of a polynomial or a Whittaker model.

The order follows the existing normalization: the unramified character with
uniformizer value `z` has absolute value `|z|` there, while the real twist
`|.|^t` has uniformizer absolute value `q^(-t)`. Decreasing real exponents
therefore correspond to increasing absolute values. Weak inequalities allow
equal-exponent characters to be grouped into a tempered block; the statement
does not require every tempered block to have rank one. The Euler polynomial
is the existing product `∏ i, (1 - C (z i : ℂ) * X)`, with no inversion or
additional shift. This order explanation is a design inference from the
Library's definitions; neither of the two obligations is a cited or proved
classification or analytic result.

`SphericalStandardLPrerequisitesStatement F` is their conjunction.
The theorem `sphericalStandardLComparison_of_prerequisites` implements the
following conditional proof. It unpacks the class polynomial certificate
into actual equivalent representatives `A`, `A0`, `J`, and `J0`. Equivalence
invariance transports the supplied spherical spectrum to `A`. The first
prerequisite chooses `d`, `z`, and the standard-module equivalence. The
rank-one character certificate is transported through equality of automorphic
classes to identify `J0` with the trivial character. A rank-one quotient
datum `e` is obtained from the pair certificate, and
`standardModuleEquivRankOne` identifies its standard module with `J0`.
The certificate holds for every presenting datum pair, so it applies to
the chosen `d` and `e`. Actual equivalence transport now gives the JPSS
certificate for the ordered principal series and trivial character.
The second prerequisite computes it, and equality of the unordered spectrum
gives the target equality.

Provenance is internal proof decomposition of the existing representation
relations and composition of their proved equivalence transport lemmas.
No additional hypothesis is added to the target statement, and the final
conditional theorem is not an unconditional proof of that target. The
remaining work is to prove the two new propositions independently.
