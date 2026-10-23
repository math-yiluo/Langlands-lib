# Convergence and rational continuation over general local fields

This module states the convergence and rational-continuation obligations for
Shahidi's intertwining integral over an arbitrary nonarchimedean local field,
including positive characteristic. All three declarations are `Prop`-valued
definitions. No analytic assertion is proved or assumed.

## Source and provenance

The original is Shahidi, *Fourier transforms of intertwining operators and
Plancherel measures for GL(n)*, Amer. J. Math. 106 (1984), 67–111,
registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Printed page 70 fixes the field, residue cardinality and normalized absolute
value. On printed page 72, equation (0.1) is

`A(s,π,w_(m,n))f(g) = ∫ f(w_(m,n) u' g) du'`.

The paragraph following it asserts convergence for sufficiently large real
part of `s` and continuation rational in `q^(-s)`. The source cites its
references [15, 19, 22] for convergence; this unit does not formalize those
proofs.

Worker 99 adapted Worker 11's published p-adic `IntertwiningStatements`
formulation to the general-field definitions in `GeneralIntertwiningFamilies`
and `IntertwiningInduced`. The compact-picture and scalar interpretations are
derived choices: the source does not specify a family of sections identifying
the induced spaces as `s` varies. The normalized induction uses the existing
factor twists `|det|^(s/2)` and `|det|^(-s/2)`. The inherited printed-exponent
issue and its source-consistency rationale remain documented in `Induction`;
this unit makes no new claim of a published erratum.

## Parameters and actual objects

The declarations lie in `Langlands.Shahidi`. They take a field `F` in universe
`uF`, a specified valuation and topology with `IsNonarchimedeanLocalField F`,
and arbitrary positive ranks `hm : 0 < m`, `hn : 0 < n`. They install the
Borel measurable structure of this topology.

Each component quantifies:

- `q : ℕ`, equal to the cardinality of the residue field of the specified
  valuation ring;
- a real absolute value `abv` and a uniformizer `ϖ`, with
  `abv ϖ = q⁻¹`, together with `abv x = 1` whenever the valuation of `x`
  is one;
- an arbitrary additive Haar measure `ν` on `F`;
- two algebraic complex modules in a common universe `uV`, independent
  of `uF`, and representations `π₁` of `GL_m(F)` and `π₂` of `GL_n(F)`;
- admissibility and algebraic irreducibility of both factors.

Admissibility is `IsAdmissible` and includes smoothness. Irreducibility is
`IsSimpleModule` for the group-algebra module associated to the representation.
There is no genericity, unitarity, supercuspidality, or norm on either carrier.
No additive character is needed for (0.1).

The unit condition on `abv` gives the open norm-one subgroup by the proved
`isOpenNormOne_of_valuation`; it is not an extra analytic premise.
`SourceSpace`, `sourceDomain`, and `sourceEval` are the existing actual
normalized induction, its convergence submodule, and evaluation.
`rectangularMeasure ν n m` is the product Haar measure on the `n × m`
coordinates of the exchanged upper radical `U'`. Thus the integrand uses
`blockWeyl m n F * intertwiningUnipotent m n F a * g`, in the order of (0.1).

## Convergence

`GeneralIntertwiningConvergenceStatement F hm hn` concludes that there is
a real `a` such that, for every `s` with `Re s > a`,
`sourceDomain ... s ... (rectangularMeasure ν n m) = ⊤`.
The bound may depend on the factors and fixed field and measure data but
works for every source section and every evaluation point.

Membership in this domain means the published smooth weak integral exists
at every `g`: each smooth-dual scalar test is integrable, and a vector
represents all those scalar integrals. It is therefore more than the
totalized value of a Bochner integral. It places no Banach-space assumption
on the algebraic representation carriers.

## Rational continuation

`GeneralIntertwiningRationalityStatement F hm hn` quantifies every actual
family `f : ∀ s, SourceSpace ... s ...` satisfying `IsGeneralFlatFamily`.
This says precisely that `f_s(k)` is independent of `s` for every
`k ∈ GL_(m+n)(O_F)`. The conclusion has two parts:

- the family lies in the convergence domain throughout a right half-plane;
- for every such `k` and each smooth functional `ℓ` of `π₁ ⊗ π₂`, there is
  `R : RatFunc ℂ` with `HasRationalContinuation q` for the scalar function
  `s ↦ generalIntertwiningCoefficient ... f k ℓ s`.

The latter function is the complex integral of `ℓ(f_s(w u'(a) k))`.
`HasRationalContinuation` requires equality with `R(q^(-s))` on a right
half-plane and nonvanishing of its denominator there. Thus a totalized
integral at a divergent parameter or rational evaluation at a pole cannot
satisfy the asserted half-plane interpretation. The convergence and
continuation half-planes can be intersected.

On the convergence domain, `generalIntertwiningCoefficient_eq` identifies
this scalar with the smooth-dual pairing of the inverse tensor flip of the
actual target value of `intertwiningInduced`, under its displayed Levi
cofinality and Haar modulus-scaling conditions. Neither condition is assumed
by the new analytic statements. Deriving them for this normalized general
local-field setting remains a separate prerequisite for that operator
reading; no such derivation is claimed here.

The restriction to `k` in the integral maximal compact is intentional.
Away from it, target covariance can contribute
`(|det h₁| / |det h₂|)^(s/2)` at `g = diag(h₂,h₁) u k`. An odd valuation
of the determinant quotient introduces an odd power of `q^(-s/2)`.
Consequently unrestricted rationality in `q^(-s)` at every `g` would exceed
this compact-picture formulation. The rational witness can depend on
both `k` and `ℓ`; there is no common-denominator or vector-valued rationality
claim.

## Combined target and boundaries

`GeneralIntertwiningAnalyticStatement F hm hn` is the conjunction of these
two statements, at the same universe parameters, field and ranks.

These statements preserve the earlier p-adic targets and extend their scope
to all fields satisfying the general local-field class. They do not prove
existence of flat extensions, Iwasawa decomposition, or the identification
of the source's compact-finite functions with the Library's smooth induced
model. They state no holomorphy or nonvanishing of a normalized operator,
no Jacquet stabilization, no local-coefficient existence, and no gamma-factor
comparison.
