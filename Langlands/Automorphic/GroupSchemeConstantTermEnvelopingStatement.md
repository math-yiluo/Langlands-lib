# Enveloping derivatives preserve vanishing parabolic constant terms

`AdelicConstantTermEnvelopingStatement` is a target proposition for proof. It is
universally quantified over the following data:

- a number field `F` and an affine group scheme `G` over `F` of locally finite
  type, smooth of relative dimension `d` (`hsmooth`);
- the structural parabolic dynamic statement `hPD`, which the Library proves
  as `GroupScheme.parabolicDynamic`;
- connected reductivity `hG`;
- a proper rational parabolic `P` of `G`;
- an element `a` of the actual enveloping algebra
  `AdelicEnvelopingAlgebra F G hsmooth`;
- an original finite plot-smooth rational function `f`.

It asserts that if the published normalized constant term of `f` along `P`
vanishes at every adelic point, then the normalized constant term of the actual
enveloping derivative `actualAdelicEnvelopingAction F G hsmooth a f` along `P`
also vanishes at every adelic point. The constant term is the published
`constantTerm` along the unipotent radical `properRationalParabolicRadicals hPD hG P`,
with the published normalized quotient measure `properParabolicQuotientMeasure`.

## Role

Getz–Hahn, Definition 6.5.1 (printed p. 166), defines cusp forms by the
vanishing of these constant terms for every proper parabolic. Definition 6.5.2
(printed p. 168) uses `A_cusp` as a `(𝔤, K_∞) × G(𝔸_F^∞)`-module. The Library
already proves that the cusp form spaces are invariant under finite right
translation (`GroupSchemeCuspidalForms`). Applied to every proper rational
parabolic, this statement supplies the remaining `𝔤`-part: the actual
enveloping action preserves the published parabolic cusp condition
`normalizedParabolicCuspidalSubrepresentation`.

The expected proof differentiates under the constant-term integral. The
quotient of the unipotent radical is compact and carries a finite measure.
Right translation by an infinite adelic point commutes with the left
integration. The derivative is the published manifold derivative of the
infinite slices.

## Provenance

This is an internal target statement, written with published Library objects
only. Getz–Hahn is cited for the role of cusp forms and their module structure;
the proposition itself is not stated there in this form. No proof is supplied
here.
