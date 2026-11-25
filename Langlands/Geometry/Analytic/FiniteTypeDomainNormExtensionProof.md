# A multiplicative norm on every finite type domain

`Langlands.Analytic.AffineAnalytification.finiteTypeDomainNormExtension`
proves the unchanged published proposition
`Langlands.Analytic.AffineAnalytification.FiniteTypeDomainNormExtensionStatement.{u,v}`.
For a complete, ultrametric, nontrivially normed field `K : Type u` and a
finitely generated commutative `K`-algebra `D : Type v` that is a domain, it
constructs a multiplicative ring seminorm `ν` satisfying

```text
∀ c : K, ν (algebraMap K D c) = ‖c‖
∀ a : D, ν a = 0 → a = 0.
```

The universes `u` and `v` remain independent.

## Implemented proof

1. Mathlib's `exists_integral_inj_algHom_of_fg` supplies a natural number
   `n` and an injective integral `K`-algebra homomorphism
   `f : P →ₐ[K] D`, where `P = MvPolynomial (Fin n) K`.
   The proof uses the integral form of Noether normalization.
2. The private homomorphism `polynomialToTate K n` evaluates the polynomial
   variables at the actual variables of `StrictTateAlgebra (Fin n) K`.
   Its composite with the inclusion into multivariable power series is
   `MvPolynomial.coeToMvPowerSeries.algHom K`. This identity is checked on
   the variables. Injectivity of the polynomial-to-power-series map then
   proves `polynomialToTate_injective`.
3. Set `C = StrictTateAlgebra.GaussAlgebraicClosure K n`. This is the
   Library's algebraic closure of the completed residue field of the Gauss
   point. It is an actual algebraically closed normed field. Its scalar
   map from the Tate algebra is injective, by `gaussClosureFaithful`, and
   its `K`-algebra structure preserves the scalar norm, by
   `gaussClosureBaseNormedAlgebra` and `norm_algebraMap'`.
   Composing the two maps gives an injective `K`-algebra homomorphism
   `j : P →ₐ[K] C`.
4. Give `D` and `C` their `P`-algebra structures through `f` and `j`.
   Put `L = FractionRing D` with its standard localization algebra and
   scalar-tower structures. The map `P → L` is injective because `f` and
   `D → L` are injective. Integrality of `D` over `P` makes it algebraic
   over `P`; `IsFractionRing.isAlgebraic_iff'` makes `L` algebraic over `P`
   as well. These injectivity statements also supply the faithful and
   torsion-free scalar actions needed by the algebraic embedding theorem.
5. Mathlib's `IsAlgClosed.lift` gives `g : L →ₐ[P] C`. Its underlying map
   is injective because `L` is a field. Thus
   `e = g.toRingHom.comp (algebraMap D L)` is an injective ring
   homomorphism from `D` to `C`.
6. Define `ν a = ‖e a‖`. The normed-field laws on `C` prove all the
   `MulRingSeminorm` laws directly. For `c : K`, compatibility of `f`,
   `g` and `j` with their scalar maps gives
   `e (algebraMap K D c) = algebraMap K C c`. The norm-preserving
   `K`-algebra structure on `C` therefore proves `ExtendsNorm K ν`.
   Finally `ν a = 0` implies `e a = 0`, and injectivity of `e` gives
   `a = 0`.

The private polynomial helpers are internal constructions for this proof.
The ambient Gauss field and its norm are imported published constructions;
no additional normed extension or embedding is assumed.

## Provenance and original sources

The target is the algebraic consequence of Berkovich's
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1(i), printed p.63 / PDF p.77, and Remark 3.4.2,
printed p.64 / PDF p.78. Surjectivity of the analytification map at the
generic point of `Spec D`, together with the affine description by
multiplicative seminorms extending the base norm, gives exactly the
seminorm with kernel zero stated here.
The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The implemented proof is an algebraic derivation using Noether
normalization and the existing Gauss algebraic closure, rather than
surjectivity of analytification. The valuation-extension input is
already implemented by the imported Gauss construction using Mathlib's
spectral norm. The corresponding original result is Temkin,
*Valued Fields* (course notes), Theorem 1.7.7, PDF pp.15–16: the valuation
of an analytic field extends uniquely to every algebraic extension.
Here it is applied inside the Gauss construction to its complete residue
field and that field's algebraic closure. The registered source is
`temkin-valued-fields-2018-course-notes`, SHA256
`60cbfd7681abcb39ee111aff005434bd6b11054089cf48a78068c97e3d53abe3`.

This module proves existence under exactly the published hypotheses. It
does not assert uniqueness of `ν`. It does not use
`AnalytificationCenterStatement`; the center-map surjectivity proof may
use this result.
