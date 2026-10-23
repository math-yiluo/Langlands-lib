# Gamma factors from nongeneric epsilon and L factors

Author: Worker 31.

This module constructs the rational gamma unit from the published nongeneric
epsilon relation, the original L-polynomial relation, and the L-polynomial
relation for the genuine smooth contragredient pair. Each of these three
existence inputs is explicit. The construction proves uniqueness, independence
of the chosen certificates, nonvanishing, and evaluation wherever the displayed
dual polynomial denominator does not vanish.

## Provenance and normalization

The contribution is derived from existing Library constructions. The classical
normalization is Jacquet–Shalika, *A lemma on highly ramified epsilon-factors*
(1985), §4.1(1), printed p.326 (PDF page 8, zero-based index 7):

\[
\gamma(s,\pi\times\sigma,\psi)
 =\epsilon(s,\pi\times\sigma,\psi)
   \frac{L(1-s,\widetilde\pi\times\widetilde\sigma)}
        {L(s,\pi\times\sigma)}.
\]

The original page was read directly. The registered source is
`jacquet-shalika-1985-ramified-factors`, SHA256
`0864a6633c3cf430f576f91eadd05a7f11d88eea1b47095943d3ea76f7c9946b`.
That passage assumes irreducible generic representations. Extending this
formula using the existing nongeneric epsilon and L relations is the derived
construction here; the citation does not prove agreement with the generic
integral gamma relation or any nongeneric factor law.

The imported epsilon relation in `LanglandsFactors` uses actual
square-integrable Langlands quotient data and the product of their generic
block epsilon factors. The imported L relation in
`LanglandsQuotientLFactorStatement` uses actual tempered Langlands quotient
data and the integral-based L-polynomial of every presenting standard-module
pair. Their distinct definitions and source normalizations are retained. No
identity between a tempered standard-module L-factor and a square-integrable
block product is assumed in this module.

`LanglandsLFactor` supplies normalization, nonvanishing and the rational unit
`langlandsPairLFactor P` with value `1/P(X)`. `PairFactors` supplies the epsilon
monomial, `rationalGammaExpression`, and its justified evaluation theorem.
`LocalFactor/WeilDelignePair` supplies the rational reflection homomorphism
`RationalReflection.subst` and the reciprocal scale; only this algebra is
reused, with no arithmetic/representation factor comparison. Finally,
`Category/Contragredient` supplies `SmoothRep.contragredient`, the smooth
linear dual with action by precomposition with the inverse group action. This
is an actual smooth contragredient, not an unproved identification with a
pullback along inverse transpose.

Write `q` for the canonical residue cardinality, `X = q^(-s)`, and
`epsilon(s) = c q^(-m s)` with `c : ℂˣ` and `m : ℤ`. Then reflection is
`X ↦ q⁻¹/X`, and the constructed rational function is

\[
  cX^m\,\frac{P(X)}{P_{\mathrm{dual}}(q^{-1}/X)}.
\]

All products, inverses and reflection in the constructor take place in units
of the rational-function field, before any spectral evaluation.

## Parameters and auxiliary character

The field is `F : PadicField.{uF} p` with its canonical topology and local-field
structure. Coefficients are complex. The additive character `ψ` is the shared
nontrivial unitary additive character and `ν` is the shared additive Haar
measure. There is no added self-duality hypothesis; the required factor
certificates refer to this exact measure. The two ranks are independently
`r + 1` and `t + 1`, so rank one, equal ranks and both unequal-rank orders are
included through the existing relations.

The representation carrier universes are `max uF uV` and `max uF uW`. The
three parameters `uF`, `uV`, `uW` remain independent. Since the scalar field is
`ℂ : Type 0`, the smooth contragredient stays in the same carrier universe.
The factor relations use block universes `uV` and `uW`. Existing classification
constructors can instead be applied with the saturated block universes
`max uF uV` and `max uF uW`; this module does not lower them.

The dual L-polynomial is certified with `ψ.scale (-1)`, namely
`x ↦ ψ(-x)`, and the same Haar measure `ν`. This is the inverse character
used by the dual Whittaker integrals. The cited classical L-factor notation
suppresses the auxiliary additive character. Here character independence
is not assumed: `IsLanglandsDualPairLPolynomial` records the precise character
choice. Comparison with another choice, or with the generic dual integrals,
remains a separate compatibility obligation.

No independent irreducibility or admissibility argument is hidden in the
constructor. Its inputs are already certificates for the nongeneric relations,
which include genuine quotient presentations. Supplying those certificates
from irreducibility, admissibility, classification and analytic factor
existence is the role of the existing conditional constructors and their
remaining hypotheses.

## Declarations and implemented proofs

The gamma declarations are in `Langlands.RankinSelberg`. The common scalar
and its coercion theorem are imported from `LocalFactor/ResidueReflection`.

- `LocalFactor.residueReflection F` is the nonzero complex reciprocal of
  `q`, using the shared `WeilDeligne.reflectionScale`. Its coercion theorem
  `LocalFactor.coe_residueReflection` identifies its value with `(q : ℂ)⁻¹`.
  This reuses the existing correspondence scalar, moved into the shared
  module, in place of the identical `padicGammaReflectionScale` definition.
- `IsLanglandsDualPairLPolynomial` is the existing nongeneric L relation at
  `π.contragredient`, `σ.contragredient`, the inverse character and `ν`. It
  installs the canonical topology and local-field instances needed to form
  those objects; it asserts no duality theorem.
- `IsLanglandsPairGammaFactor G` means there exist an epsilon pair `(c,m)`, an
  original polynomial `P`, and a dual polynomial `Pdual`, each satisfying its
  exact relation, with `G` equal to the displayed rational gamma expression.
- `LanglandsPairGammaInput` is the conjunction of the three intrinsic
  existence propositions. It is a `Prop` definition, not an assumed theorem.
- `langlandsPairGammaUnit` takes the three certified witnesses and forms the
  epsilon unit times the image of the dual L-unit under rational reflection,
  divided by the original L-unit. `Units.map` preserves invertibility.
- `langlandsPairGammaUnit_eq_expression` unfolds the dual adapter and unit
  coercions, rewrites both L-units as inverses of polynomial images, and uses
  preservation of inverse and polynomial substitution by rational reflection.
  Double inverse cancellation and commutative multiplication give exactly
  `rationalGammaExpression`.
- `langlandsPairGammaFactor` takes `LanglandsPairGammaInput` and chooses one
  witness for each of its three existential proofs. It returns the constructed
  unit together with its `IsLanglandsPairGammaFactor` certificate. Choice is
  applied only to these supplied existence proofs.
- `IsLanglandsPairGammaFactor.unique` identifies the epsilon witnesses by the
  published epsilon uniqueness theorem and both polynomial witnesses by the
  published L uniqueness theorem, then rewrites the expressions.
  `langlandsPairGammaFactor_independent` applies this equality and `Units.ext`
  to show independence of the input proofs and selected witnesses.
- `IsLanglandsPairGammaFactor.ne_zero` rewrites any certified rational value
  as the coercion of the constructed unit, then uses `Units.ne_zero`.
- `langlandsPairGammaUnit_eval` assumes only that
  `Pdual.eval (spectralPoint q (1-s)) ≠ 0`. It uses `q > 1`, the identity
  `q⁻¹ / spectralPoint q s = spectralPoint q (1-s)`, and the published
  `eval_rationalGammaExpression` theorem. The result is
  `epsilonMonomial q c m s * P.eval (spectralPoint q s) /
  Pdual.eval (spectralPoint q (1-s))`. No nonzero assumption on `P` at this
  point is needed for that polynomial quotient identity. Interpreting a ratio
  of separately evaluated L-factors can require additional regularity.

## Remaining obligations

The module does not prove the three input existence propositions. Published
classification-based constructors for epsilon and L can supply their
certificates once the required classification, exhaustion and analytic
hypotheses are proved, including for the actual contragredient pair. The
module also does not prove agreement with generic JPSS gamma factors,
character independence of L, contragredient compatibility of generic
Whittaker models, or twist and character-change laws. Those remain separate
factor-law and analytic responsibilities. Evaluation is asserted only on the
displayed denominator domain; cancellation can enlarge the actual regular
domain, and no total evaluation rule at poles is claimed.
