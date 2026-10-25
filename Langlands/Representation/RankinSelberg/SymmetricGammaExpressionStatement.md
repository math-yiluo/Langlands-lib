# Canonical symmetric gamma expression from certified pair factors

`Langlands.RankinSelberg.SymmetricGammaExpressionStatement.{uF,uV,uW}`
is a proposition definition. It states a conditional characterization of every
certified rational gamma factor of a pair of actual representations. This module
does not prove the proposition.

## Statement and conventions

For every prime `p`, every `F : PadicField p` with its canonical topological
data, every nontrivial continuous unitary additive character `ψ`, and every
supplied `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`,
take representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)` on independent
complex-module carriers. The field and the two carriers have independent
universes `uF`, `uV`, and `uW`. All positive ranks, including rank one, equal
ranks and both orders of unequal ranks, are included.

Assume `PadicSymmetricGammaConstructionInput F ψ ν.val π σ`. For arbitrary
`e = (c,m) : ℂˣ × ℤ` and polynomials `P, Pdual : ℂ[X]`, assume:

1. `IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e`;
2. `IsPadicSymmetricLPolynomial F ψ ν.val π σ P`;
3. `IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
   (inverseTransposePullback π) (inverseTransposePullback σ) Pdual`.

Then, for every `G : RationalFunctions`, the proposition asserts

```text
IsPadicSymmetricGammaFactor F ψ ν.val π σ G
  ↔ G = rationalGammaExpression (LocalFactor.residueReflection F) c m P Pdual.
```

Here `q = F.canonicalTopologicalData.residueCardinality`, and
`LocalFactor.residueReflection F` is the actual complex unit `q⁻¹`.
The existing expression is the rational function

```text
c X^m P(X) / Pdual(q⁻¹ / X).
```

At the spectral variable `X = q^(-s)`, the reflection corresponds to `1-s`;
the ratio is `ε(s, π × σ, ψ) L(1-s, πⁱ × σⁱ) / L(s, π × σ)`.
This equality is in the rational function field, so no pointwise
nonvanishing assumptions are added. The central minus-one sign remains in the
existing functional-equation relation, outside the gamma factor.

The duals are the existing inverse-transpose pullbacks on the original
carriers, not a chosen equivalent representation or a smooth contragredient.
The dual character is exactly `x ↦ ψ(-x)`. The dual polynomial certificate
uses the same additive Haar measure `ν.val`. The L-polynomial relation accepts
this underlying measure directly; no self-dual measure for `ψ.scale (-1)` is
assumed or constructed. Supplying `ν` also makes no assertion that self-dual
measures exist.

The symmetric relations and the construction input use the existing convention
of placing the larger rank first. Their common branch is `(π,σ)` when `n ≤ r`
and `(σ,π)` otherwise. This statement introduces no additional rank-exchange
identity and redeclares no constructor.

## Provenance and remaining obligations

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464: Theorem (2.7), printed pages 390–391, and section (2.12), printed
page 403. Source ID: `jpss-1983-rankin-selberg`; retained PDF:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These pages were read visually. No separate JPSS errata file was found in the
available project notes or literature collection.

Theorem (2.7)(i)–(ii) gives the analytic and normalized-generator assertions
for representations of Whittaker type, including the inverse-transpose pair.
Part (iii) gives the epsilon monomial and normalized functional equation in
equal and unequal ranks, with complementary blocks in the latter case.
Section (2.12) supplies the larger-rank-first convention for L and epsilon
factors. The present iff is derived packaging of the Library's conditional
constructions and uniqueness, not a verbatim theorem in that source.

In particular, original and dual analytic conclusions and epsilon existence
remain contained in `PadicSymmetricGammaConstructionInput`. After choosing its
rank branch, this predicate also retains the original standard/inverse-standard
Whittaker types and self-duality. It does not derive these inputs from bare
representations. No irreducibility hypothesis is added.

A future proof should reduce the common rank-order branch and derive dual
Whittaker type by `isOfWhittakerType_firstDual` and
`isOfWhittakerType_secondDual` from `GammaFromWhittakerType`. At a compatible
quotient measure, specialize the intrinsic polynomial certificates and apply
`IsEqualRankEpsilonFactor.gammaFactor` or
`IsUnequalRankEpsilonFactor.gammaFactor`, using the original and dual analytic
inputs. With `coe_residueReflection`, these certify the displayed expression.
`IsPadicSymmetricGammaFactor.unique` then compares any certified `G` with that
expression; the converse follows by substitution. The existing theorem
`pairGammaFactor_eq_expression` in `PairFactors` only identifies the constructed
unit and alone does not certify an arbitrary symmetric `G`.

Proving this certificate bridge is separate from establishing its analytic
inputs, functional equations, epsilon existence, or a closed input-instantiation
statement. Those substantive obligations remain with their existing tasks.
