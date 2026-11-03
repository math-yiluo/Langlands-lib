# Coefficients on actual normalized product induction

This module constructs the coefficient map of Waldspurger V.1 on the actual
normalized induction from the product parabolic. It composes the proved product
induction comparison with the proved same-parabolic integral duality. Its values
are locally constant functions on the ambient group. A diagonal integral formula,
integrability, the full product-action translation law, common open bi-invariance
and equality of the actual coefficient images are proved.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, is the motivating source, registered as
`waldspurger-2003-plancherel`.

I.3, printed p.243 (PDF p.9), defines normalized induction using positive
half-modulus left covariance and uniform open right invariance. It identifies
induction of the smooth contragredient with the smooth contragredient of
induction by the bilinear quotient integral. V.1, printed p.288 (PDF p.54),
defines

\[
 L(\omega,P)=I_{P\times P}^{G\times G}(E\otimes\check E),
 \qquad
 E_P^G(v\otimes\ell)(g)=\ell((I_P^G\omega)(g)v),
\]

using the natural identifications with the tensor of the two inductions and
then with the coefficient tensor of induction. It also identifies the image
with the smooth coefficient space of induction. Both original passages were
read directly for this construction.

This module is a derived adapter for these definitions on the Library's actual
normalized induced functions. It reuses
`normalizedProductInductionTensorEquiv` and
`normalizedInductionDualTensorEquiv`; neither comparison is assumed. The
diagonal contraction formula and its extension from pure tensors follow from
their proved evaluation and pairing laws. The scope of arbitrary actual
topological subgroup data is justified by those Library constructions, rather
than attributed verbatim to the reductive-group source.

## Objects, hypotheses and conventions

Let `G : Type uG` be a locally compact nonarchimedean group, and let `P`, `M`
and `U` be actual subgroups of `G`, with
`h : IsSemidirectDecomposition P M U` and closed `U`. Let
`A : SmoothRep.{0, uG, uV} ℂ M`. The group universe `uG` and inducing-carrier
universe `uV` are independent.

Write `I(A)` for `(normalizedInductionFunctor h hU).obj A`.
`productInducedCoefficientObject h hU A` is precisely

\[
 I_{P\times P}^{G\times G}(A\boxtimes A^\vee).
\]

Its product subgroups are literal `Subgroup.prod` subgroups; the semidirect
decomposition is the proved `h.prod h`, the closed radical is `U.prod U`, and
the inducing smooth object is `productLeviObject A A.contragredient`. The
normalized product action uses the actual product Haar half-character. The
underlying functions take values in `A ⊗[ℂ] A.contragredient`, have the canonical
left covariance, and are uniformly invariant under an open right subgroup.
The representation acts by right translation in `G × G`.

The product comparison additionally requires `SecondCountableTopology G` and
compactness of the actual quotient `Induction.LeftQuotient P`.
For the integrability and integral coefficient formula, the following inputs
are explicit:

- `G` is Hausdorff and carries its Borel measurable structure;
- `P` is closed and has a `LocallyCompactSpace` instance;
- `hG : ∀ g : G, Measure.modularCharacter g = 1`;
- for every `q : P`,
  `Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)`.

The tensor comparison with the coefficient tensor, and therefore the
coefficient map, additionally use continuity of `h.projection` and
`hA : A.IsAdmissible`. No irreducibility of `A` or of its induction is assumed.
Integrability of the diagonal contraction does not require inducing
admissibility or continuity of the Levi projection.

All integrals below use the single measure
`μ = normalizedInductionBruhatMeasure hP hG` on `⊤ : Subgroup G`. This is the
previously constructed compact-quotient Bruhat-density measure, fixed
independently of `A`. Its stated positivity and modular-covariant integral
translation properties are inherited from
`normalizedInductionBruhatMeasure_spec`. This measure is not asserted to be
ambient Haar. Its absolute scale and agreement with all manuscript Haar
choices are not established here.

## Diagonal contraction and integrability

`productInducedCoefficientIntegrand h hU A g` is a complex linear map from the
actual product-induced space to scalar functions on the top subgroup. For a
product-induced function `F`, it is

\[
 J_g(F)(k)=\operatorname{ev}_A(F(kg,k)),
 \qquad
 \operatorname{ev}_A(v\otimes\ell)=\ell(v).
\]

The contraction is `TensorProduct.lift (smoothDualPairing A.representation).flip`.
This is a complex bilinear pairing; no complex conjugation occurs. The
additivity and scalar linearity of evaluation and contraction prove that `J_g`
is linear.

Let `T = normalizedProductInductionTensorEquiv h h hU hU A A.contragredient`.
Its pointwise evaluation law proves
`productInducedCoefficientIntegrand_tensor`:

\[
 J_g(T(f\otimes f^\vee))(k)=f^\vee(k)(f(kg)).
\]

The proof applies the contraction to
`normalizedProductInductionTensorEquiv_tmul_eval`. Thus the order of the vector
and functional and the right translation are fixed by the actual induced
evaluation.

`productInducedCoefficientIntegrand_integrable` proves `Integrable (J_g F) μ`
for every actual product-induced `F`. Surjectivity of `T` expresses `F` as the
image of a tensor, and tensor induction reduces to pure tensors and sums.
For pure tensors the preceding formula and
`normalizedInductionCoefficient_integrable` give integrability. For sums,
linearity of `T` and `J_g` and `Integrable.add` finish the proof. Consequently
the integrals below are actual integrals of integrable functions.

## Tensor comparison and coefficient map

`productInducedCoefficientTensorEquiv` is the representation equivalence

\[
 E = \texttt{normalizedInductionDualTensorEquiv}\circ T^{-1}
 \;:\;
 L(A,P)\simeq I(A)\otimes I(A)^\vee.
\]

Both maps are the proved actual `G × G` representation equivalences.
`productInducedCoefficientTensorEquiv_tensor` records cancellation of `T`.
In particular, if `D : I(A)^\vee ≃ I(A^\vee)` is the integral-characterized
duality, this composite sends `T(f ⊗ fdual)` to
`f ⊗ D.symm(fdual)`.

`productInducedCoefficientMap` is `normalizedCoefficientMap` composed with
`E`. Its source is the actual product-induced space, and its target is
`LocallyConstant G ℂ`. `productInducedCoefficientMap_tensor` states its
compatibility with the previously constructed coefficient map on the tensor of
the two inductions. The pure-tensor formula
`productInducedCoefficientMap_tmul` is therefore

\[
 E_P(T(f\otimes f^\vee))(g)
   =\int_k f^\vee(k)(f(kg))\,d\mu(k).
\]

It follows by cancellation of the product comparison and the integral
coefficient formula of `normalizedInductionDualCoefficientMap_tmul`.
`productInducedCoefficientMap_integral` proves the formula on every actual
product-induced function:

\[
 E_P(F)(g)=\int_k J_g(F)(k)\,d\mu(k).
\]

The proof again uses surjectivity of `T` and tensor induction. The pure case is
the preceding formula. In the sum case, the proved integrability permits
`integral_add`, and linearity of the coefficient map and contraction gives the
result. This formula depends on `F` itself and introduces no choice of tensor
expansion into the definition.

## Translation, common invariance and image

`productInducedCoefficientMap_action` proves, for every actual product-induced
`F` and every `x = (a,b) : G × G`,

\[
 E_P(x\cdot F)(g)=E_P(F)(b^{-1}ga).
\]

The proof evaluates the intertwining law of `E` on `F`, then applies
`coefficientTensorMap_action`. It concerns the full actual product-induced
action, not only its pure-tensor generators.

`productInducedCoefficientMap_biInvariant` gives one open subgroup `K` of `G`
such that `E_P(F)(k*g*l)=E_P(F)(g)` for all `k,l : K` and all `g : G`. It
applies the existing common bi-invariance theorem to `E F`.

`range_productInducedCoefficientMap` identifies its linear-map range with
`LinearMap.range (normalizedCoefficientMap h hU A)`. One containment applies
`E`; the other applies `E.symm` and cancels their composite. By the imported
`range_coefficientTensorMap`, this is the span of the actual smooth matrix
coefficients of `I(A)`. No injectivity or irreducibility of parabolic induction
is inferred.

## Remaining scope

This is the coefficient construction for the Library's actual normalized
induction, under the hypotheses displayed above. Reductive rational-point
realization, the full-parabolic versus Levi-inflated modulus comparison when
specializing the source, the manuscript-wide absolute measure normalization,
compact pictures, transport between equivalent inducing representatives, smooth
twist families and stabilizer descent remain separate obligations. This module
does not assert Schwartz membership, wave-packet estimates, isometry, spectral
finiteness, Plancherel inversion or completion of the standing program.
