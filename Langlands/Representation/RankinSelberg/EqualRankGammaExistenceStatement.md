# Equal-rank JPSS gamma-factor existence

Author: Worker 358. The binder scope and private valuative-topology proof are
adapted from Worker 11's published `FunctionalEquationStatement` module.

The paired Lean file defines, but does not prove,
`Langlands.RankinSelberg.EqualRankGammaExistenceStatement.{uF,uV,uW}
(F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop`, with
`{p : ℕ} [Fact p.Prime]`. It isolates a derived intermediate assertion from
the equal-rank case of JPSS Theorem 2.7(iii), before normalization by the
L-polynomials. It is not a verbatim statement from the source or an axiom.

## Exact scope

The proposition has precisely the binder scope of the published
`EqualRankFunctionalEquationStatement F T n`. It uses every supplied
`T : F.TopologicalData`, with `q = T.residueCardinality` and
`abv = normalizedAbsoluteValue T`, and every positive rank `n+1`, including
rank one when `n = 0`. The field and the two representation carriers have
independent universes `uF`, `uV`, and `uW`.

In the same order as that target, the definition installs `T.topology`,
`T.valuativeRel`, `T.localField`, the additive right uniform space,
`isUniformAddGroup_of_addCommGroup`, the derived `NonarchimedeanAddGroup`
instance, and the Borel measurable structures and `BorelSpace` instances
on `F.Carrier`, `GL_(n+1)(F)`, its upper unipotent subgroup, and
`LeftUnipotentQuotient n F.Carrier`. The private theorem
`valuative_nonarchimedean` supplies the same Prop-valued instance as in the
published target: the valuative topology's basis of open submodules yields
open additive subgroups inside each neighborhood of zero. Its proof uses
`IsLinearTopology.hasBasis_open_submodule`; it adds no hypothesis.

With those instances, the proposition quantifies over:

1. Every `ψ : UnitaryAdditiveCharacter F.Carrier`, a continuous nontrivial
   additive character valued in the unit circle, and the instance binder
   `Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)`.
2. Every measure `μ` on `LeftUnipotentQuotient n F.Carrier` satisfying
   `IsCompatible (upperUnipotent (n+1) F.Carrier)
   (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ`.
   These are the existing normalized ambient and subgroup Haar measures.
3. Every scalar `ν : AdditiveHaarMeasure F.Carrier` with `IsSelfDual ψ ν`.
4. Every `V : Type uV` and `W : Type uW`, each with `AddCommGroup` and
   `Module ℂ` instances, and every representation `π` on `V` and `σ` on `W`
   of `Langlands.GeneralLinear (n+1) F.Carrier`.
5. The hypotheses `IsOfWhittakerType n (standardCharacter ψ n) π` and
   `IsOfWhittakerType n (inverseStandardCharacter ψ n) σ`. The existing
   predicate requires admissibility, finite generation over the group
   algebra, and an exactly one-dimensional space of functionals. It permits
   reducible representations and infinite-dimensional carriers.
6. Every `ℓ : glFunctionals ψ n π` and
   `ℓ' : glInverseFunctionals ψ n σ` with `ℓ.val ≠ 0` and `ℓ'.val ≠ 0`.

The conclusion is exactly

```lean
∃ G : RationalFunctions,
  EqualRankGammaEquation T.residueCardinality ψ
    (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' G
```

The module imports and uses `EqualRankGammaEquation` from `GammaFactor`
without modifying or replacing it. The existential choice of `G` occurs
after the measures, representations, and functionals and before the
coefficient vectors and Schwartz–Bruhat tests inside that predicate. No
independence from those earlier choices is asserted by this statement.

## Content of the existing conclusion

For the specified data, `EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G`
asserts that there is `ζ : ℂˣ` with all the following properties:

- `HasModelMinusOneScalar σ ℓ' ζ`: every function `f'` in the specified
  coefficient image satisfies `f'(-g) = ζ f'(g)`.
- Some `R` in `equalRankRationalValues q ψ abv μ π σ ℓ ℓ'` is nonzero.
  Thus this is a nonzero rational continuation of an actual integral for
  some coefficient vectors and a Schwartz–Bruhat test.
- For every `f : (coefficientModel π ℓ).toSubmodule`,
  `f' : (coefficientModel σ ℓ').toSubmodule`, and Schwartz–Bruhat function
  `Φ` on `Fin (n+1) → F.Carrier`, there are a Schwartz–Bruhat `Φhat` and
  rational functions `R`, `Rdual` such that `IsRowFourierPair ψ ν Φ Φhat`,
  `R` continues `equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ`,
  `Rdual` continues `dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat`,
  and `GammaFunctionalEquation q ζ n G R Rdual` holds.

Here the Fourier pairing is the actual plus-sign row transform with the
coordinate product of `ν`. The dual coefficient functions are the existing
transforms `f(g) ↦ f(w · transpose(g⁻¹))`, with inverse additive character.
`HasRationalContinuation` means agreement with rational evaluation on a
right half-plane where the denominator is nonzero. Writing `X_s = q^(-s)`,
the last condition is

`Rdual(X_(1-s)) = ζ^n · (G(X_s) · R(X_s))`

for every complex `s` for which the denominators of `R` at `X_s`, `Rdual`
at `X_(1-s)`, and `G` at `X_s` are nonzero. The proposition includes this
continuation data; it does not separately assert absolute convergence.

## Source and derived provenance

The registered original is H. Jacquet, I. I. Piatetski-Shapiro, and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, source ID `jpss-1983-rankin-selberg`. Retained file:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Its verified SHA256 is
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 391, 395, and 396 were read visually (one-based PDF pages
26, 30, and 31). No source erratum note was found in the checked workspace,
project, or supplied Library `notes/errata` locations.

Theorem 2.7(iii), display (1), printed p.391, gives the equal-rank normalized
functional equation with `ε(s) = c q^(-ms)` and the sign
`ω_σ(-1)^(r-1)`. Multiplying by the dual L-factor and setting

`γ(s) = ε(s) L(1-s, π^ι × σ^ι) / L(s, π × σ)`

gives the unnormalized equation used here. The `ι` denotes inverse-transpose
pullback, matching the actual transformed models; this statement does not
identify it with a contragredient by definition. With the L-polynomials
`P`, `Pdual` of Theorem 2.7(ii), the resulting expression is the rational
function `c X^m P(X) / Pdual(q⁻¹ X⁻¹)` in `X = q^(-s)`. Those polynomials
and the epsilon monomial explain the relation to the source; they are not
hypotheses or conclusions of this target.

Section 2.8, printed p.395, reduces the unequal-rank cases to one block;
that reduction is outside this equal-rank target. Section 2.9, printed
pp.395–396, separately shows that an existing epsilon factor must be a
monomial. Section 2.10, printed p.396, supplies the direct intermediate
route: (2.10.2) and (2.10.3) give matching right-translation equivariance
for the original and Fourier-transformed dual integrals. The Proposition
there states that the corresponding trilinear-form space has dimension
one outside finitely many values of `q^(-s)`, for pairs of Whittaker type.
Together with rational continuation and nonzero integral data from
Theorem 2.7(ii), this explains independence of the ratio from
`(W, W', Φ)` and its rational dependence on `q^(-s)`. The nonzero-continuation
clause retained in the existing gamma predicate is supported by the
nonzero fractional-ideal generator in Theorem 2.7(ii), at the top of p.391.
These are source justifications for this derived statement, not assumed
Lean prerequisites or an implemented proof.

The source sign is interpreted on the second coefficient image. In the
possibly reducible Whittaker-type scope, central translation preserves the
one-dimensional functional space, so a nonzero functional is an eigenvector
for that translation. Its scalar is nonzero since translation is invertible.
The coefficient image therefore has scalar central action even when the
original carrier does not. This is derived reasoning, not an added central
character hypothesis. For irreducible `σ`, `ζ` agrees with `ω_σ(-1)`;
with source rank `r = n+1`, its exponent `r-1` is exactly the Lean exponent
`n`.

Only the proposition and the private instance proof are supplied here.
Gamma existence, Fourier closure, rational continuation, and the required
trilinear comparison remain proof obligations. Epsilon existence,
L-factor normalization, Fourier closure, and trilinear-form uniqueness are
not added as hypotheses, nor is the gamma-existence conclusion itself.
