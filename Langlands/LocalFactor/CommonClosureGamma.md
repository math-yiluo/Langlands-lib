# Conditional gamma and tensor-pair factors in a common closure

This module constructs the measure-dependent gamma value
\[
  \gamma_{\epsilon}(s,A,\psi,\mu)
   =\epsilon_{\mathrm{WD}}(s,A,\psi,\mu)
      \frac{L(1-s,A^\vee)}{L(s,A)}
\]
from an explicitly supplied local-constant system. The epsilon factor is the
full spectral value from `CommonClosureWeilDeligne`, including the determinant
on the actual invariant quotient. Numerical gamma values require both
individual L-factors to be regular. Pair epsilon and gamma use the actual
Weil–Deligne tensor product.

## Arithmetic and conditional inputs

Fix a finite p-adic field `F` and a finite intermediate field
`E : CommonClosure.Extension F` in its specified algebraic closure. The
imported `Pair F E` is the existing finite-dimensional complex Weil–Deligne
representation on the actual Weil subgroup fixing `E`, with covariance
character equal to the restriction of the actual base norm. Its carrier
universe is `max uF uV`. All pair inputs in this module use that common carrier
universe, so one supplied system can evaluate their ordinary exact classes
and tensor products. No semisimplicity hypothesis is imposed.

Write `I = inertia F E`, the kernel of the actual restricted base degree,
and `q = residueCardinality F E`, the residue cardinality of the canonical
intermediate-field realization. A supplied `Phi : GeometricFrobenius F E`
satisfies `normCharacter F E Phi = q^(-1)`. The imported definitions use the
base cardinality and base degree together for the ordinary spectral twist,
and the intermediate-field cardinality for the Euler and quotient evaluations.
This module preserves that distinction.

Every conditional constructor explicitly takes a reciprocity family `e`, an
assignment `epsilon`, a proof `hε : NonabelianSystem.IsSystem F e epsilon`,
the actual additive character and regular additive Haar measure, and continuity
of the underlying ordinary representation. The system property includes the
specified reciprocity normalization. No reciprocity map, epsilon system,
Frobenius element, or self-dual measure is constructed or selected here.
The measure is the supplied arbitrary Haar measure; these constructors use
Deligne's measure-dependent spectral convention. The separately defined
Langlands half-shift convention is not redefined.

## Regular values and the full correction

Let
\[
 P_A(X)=\det(1-Xr_A(\Phi)\mid(\ker N_A)^I),\qquad
 z_s=\exp(-s\log q).
\]
`RegularPoint F E A Phi` is an alias of the published
`WeilDeligne.SpectralLRatioRegularPoint`. It consists exactly of the complex
parameters satisfying
\[
 P_A(z_s)\ne0,\qquad P_{A^\vee}(z_{1-s})\ne0.
\]
The dual is the actual contragredient pair with negative-transpose monodromy.
The spectral parameters are nonzero complex units. The domain is not asserted
to be maximal after cancellation of the quotient; both individual poles remain
excluded.

`lRatioValue` specializes the published `spectralLRatioValue`, giving
`L(1-s,A dual)/L(s,A)` as a complex unit. `lRatioValue_eq` unfolds the spectral
evaluations and uses `inv_div_inv` to expose its scalar value
`P_A(z_s)/P_(A dual)(z_(1-s))`. The imported `WeilDelignePair` identifies the
reflection with the rational substitution `X -> q^(-1)/X`.

`conditionalGammaValue` multiplies that ratio by
`CommonClosureWeilDeligne.conditionalEpsilonValue` at the same spectral
parameter. The theorem `conditionalGammaValue_formula` displays the full
scalar expression
\[
 \epsilon_{\mathrm{ordinary}}(s,[r_A],\psi,\mu)\,
 \det\!\left(-z_s r_A(\Phi)\mid V_A^I/(\ker N_A)^I\right)
 \frac{P_A(z_s)}{P_{A^\vee}(z_{1-s})}.
\]
The ordinary value is the supplied assignment evaluated on the actual
continuous exact virtual class after its norm twist. The quotient and its
operator are the imported actual constructions; no scalar correction is an
independent input. The formula follows by unfolding the product, the imported
quotient determinant identity, and `lRatioValue_eq`. Its complex-unit codomain
records nonvanishing on the specified domain. This module does not construct
a rational model of the full epsilon or gamma function.

## Intrinsic invariance

A private polynomial helper transports the regular domain along equalities of
the two Euler polynomials, using `Equiv.subtypeEquivRight`. It preserves the
complex parameter. Its separate value lemma keeps the implementation proof
independent of the more elaborate arithmetic types.

`regularPointEquiv` applies this helper to the Euler-polynomial equalities for
a genuine pair equivalence and its contragredient equivalence.
`regularPointEquiv_val` records that the parameter is unchanged.
`lRatioValue_eq_of_equiv` rewrites the explicit polynomial quotient; combining
it with the imported full epsilon invariance proves
`conditionalGammaValue_eq_of_equiv`.

`eulerPolynomial_eq_of_frobenius` uses the imported fact that two supplied
geometric Frobenius elements differ by inertia and that the kernel operator
is constant on this coset. Applying it also to the dual gives
`regularPointFrobeniusEquiv`. Its value lemma again preserves the parameter.
`lRatioValue_eq_of_frobenius` follows by rewriting the two polynomials, and
`conditionalGammaValue_eq_of_frobenius` combines it with the imported full
epsilon lift-independence identity. These are invariance under two supplied
lifts in the same actual group, not a Frobenius existence theorem or a
comparison between separately constructed Weil groups.

`conditionalGammaValue_of_monodromy_zero` uses the imported zero-monodromy
identity for full epsilon. The quotient correction becomes one, leaving the
ordinary supplied-system spectral value multiplied by the same reflected ratio.

## Tensor-pair factors

`tensor_isContinuous` specializes the published theorem
`Weil.OperationClosure.continuous_tensor` to the ordinary representations of
the two pairs. That theorem proves continuity of the diagonal tensor action
through the continuous bilinear tensor map on endomorphisms. Thus the
continuity needed for the exact class of the tensor is derived from the two
input continuity proofs.

`conditionalPairEpsilonValue` evaluates the imported full epsilon constructor
on `WeilDeligneRepresentation.tensor A B`. Its monodromy is exactly
`N_A tensor 1 + 1 tensor N_B`, so its correction uses the quotient of tensor
inertia invariants by the inertia-fixed kernel of that full monodromy.
`conditionalPairGammaValue` similarly evaluates `conditionalGammaValue` on
the tensor, using the tensor's own common regular domain and its actual dual.
`conditionalPairGammaValue_eq` records the product of pair epsilon with that
tensor L-ratio. There is no product-of-separate-epsilons formula.

The pair epsilon and gamma equivalence theorems apply the corresponding
single-pair identities to the published `tensorEquiv`. Both tensor legs may
be replaced by equivalent pairs; gamma transports its regular point by the
induced tensor equivalence. The single-pair lift-independence identities also
apply directly to a tensor. Pair L-factors and their regular evaluation remain
the imported constructors from `WeilDelignePair`; no duplicate L-factor
implementation is introduced.

## Sources and scope

The registered original is John Tate, *Number theoretic background* (1979),
Corvallis Part II, literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The retained original was read directly: sections 3.5.1–3.5.4, printed p.16 /
PDF p.25, give the spectral twist and dual `1-s` convention; sections
4.1.5–4.1.6, printed pp.20–21 / PDF pp.29–30, give the tensor monodromy,
Euler reciprocal, and quotient-determinant correction reused here.

The gamma product, safe common domain, domain equivalences, and tensor
specializations are derived compositions of these conventions and the named
Library constructions. The cited global functional equation is not asserted
as a local gamma theorem. Proofs in this module establish only intrinsic
identities needed to use the constructed values.

The scope is finite p-adic fields, complex coefficients, a fixed common closure,
and the stated common carrier universe. This conditional construction does not
prove system existence, select a system from an unproved proposition, compare
closures or standalone extension Weil groups, establish a local functional
equation, or evaluate a pole. It is one definition component of the arithmetic
local-factor framework.
