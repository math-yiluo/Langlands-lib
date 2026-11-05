# Finite compact values and bounds for actual product coefficients

This module constructs the compact restriction of the actual normalized
product-induced function and proves its finite-image and diagonal contraction
bounds. It supplies the compactness and covariance step toward Waldspurger's
Lemma VI.2.2. The Levi matrix-coefficient bound is an explicit analytic premise
of the estimate, with its proof still required by the Plancherel program.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, Lemma VI.2.2 and its proof, printed
pages 298–299 / PDF pages 64–65. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The source first reduces to fixed compact-model vectors with varying unitary
unramified character. It writes their induced coefficient as an integral on
K, applies parabolic covariance, bounds the Levi pairing uniformly on the
finite-dimensional spaces of vector values, and invokes III.1.2 and II.1.6.

The present contribution is a derived adapter. It treats every vector of the
original product-induced function space by restricting its tensor values to
K × K. Local constancy and compactness give a finite range. Tensor induction
extends any given pure Levi coefficient estimate to all those values. This
recovers the finite-values and covariance part of the source route without
assuming a tensor decomposition of the induced vector, finite dimensionality
of its carrier, or irreducibility. The family reduction, III.1.2, integration
estimate, and II.1.6 application remain separate obligations.

## Actual objects and assumptions

`CoefficientTensor A` is the existing algebraic tensor
`A ⊗[ℂ] SmoothDual A.representation`. Its coefficient at m is the linear
extension of `v ⊗ ell ↦ ell(A.representation m v)`. The pairing is complex
bilinear, with no conjugation.

For the first two lemmas, L is any topological group, A is its canonical
`SmoothRep ℂ L`, and ξ is a real-valued function. The analytic premise is

```
for each v : A and ell : SmoothDual A.representation,
there is C > 0 such that for every m,
  norm (ell.val (A.representation m v)) <= C * xi m.
```

`coefficientTensorMap_bound` needs this premise alone.
`coefficientTensorMap_bound_finite` additionally assumes ξ is nonnegative and
the supplied set of tensors is finite. The premise is not classified as a
structural input or proved by this module.

The compact restriction uses a locally compact nonarchimedean group G,
actual subgroups P, M and U, an actual semidirect decomposition
`h : IsSemidirectDecomposition P M U`, closedness `hU` of U, a canonical
smooth representation A of M, and an open subgroup K of G. The group universe
`uG` and representation-carrier universe `uV` are independent.

`compactValue h hU A K F (k1,k2)` evaluates the original vector
`F : productInducedCoefficientObject h hU A` at `(k1,k2) : G × G`.
The imported product-induced object is actual normalized induction from
`P.prod P` of `productLeviObject A A.contragredient`.
Its value carrier is exactly `CoefficientTensor A`.

The local-constancy lemma needs no further hypothesis. Finite range needs
`hK : IsCompact (K : Set G)`. The contraction and factorization identities
add second countability of G, used by the existing theorem identifying the
product half-modulus and inducing action with the product of the factor
actions. The bound uses compactness of K, nonnegativity of ξ on M, and the
pure Levi coefficient estimate above. The source-form corollary also assumes
`IsUnimodularModulus U hU`, so the full parabolic half-character factors
through the Levi projection.

No result in this module needs closedness or local compactness of P,
admissibility, irreducibility, an ambient modular-character identity, a Borel
structure, or a measure. The bound quantifies over every supplied
factorization `k*g = q*k1`; it does not assume that all such factorizations
exist. A source application must produce them from its actual Iwasawa data.

## Implemented deductions

`coefficientTensorMap_bound` uses tensor induction. The pure case is the
analytic premise. For a sum of tensors, the triangle inequality and addition
of their positive constants give a bound with constant C+D.

`coefficientTensorMap_bound_finite` chooses a coefficient constant for every
tensor. The image of the supplied finite set under this choice is bounded
above by some B. The positive number `max 1 B` works for the entire set,
using nonnegativity of ξ. There is no norm or topology on the representation
carrier in this argument.

`compactValue_isLocallyConstant` composes actual induced evaluation with the
continuous inclusion `K × K → G × G`. With compact K, the product is compact,
so `compactValue_range_finite` follows from the finite-range theorem for
locally constant functions on a compact space.

Write `ev(v ⊗ ell) = ell(v)` and let χP be the existing positive closed
half-character of U on P. `contraction_inducing` proves

```
ev(inducingRepresentation (q,1) t)
  = chiP(q) * coefficientTensorMap A t (h.projection q).
```

It rewrites the product inducing action to the actual product of the two
factor inducing actions. On a pure tensor the second factor acts at 1, and
linearity of ell gives the formula. The additive case uses linearity of
both the action and contraction. The local transparency setting in this
proof only reconciles the canonical bundled tensor carrier's module
instances with the concrete tensor instances.

`integrand_factorization` applies the original induced-function covariance
at `(q,1)*(k1,k)` when `k*g=q*k1`, then applies the contraction identity.
Consequently, for the unchanged imported diagonal integrand,

```
integrand h hU A K g F k
  = chiP(q) * coefficientTensorMap A
      (compactValue h hU A K F (k1,k)) (h.projection q).
```

`integrand_bound` applies the finite tensor estimate to the range of this
actual compact restriction. It produces a single C>0, depending on F and
the supplied Levi estimate, such that for every g, k, k1 and q with the
stated factorization,

```
norm (integrand h hU A K g F k)
  <= norm (chiP q) * (C * xi (h.projection q)).
```

The constant is chosen before all four factorization variables.

`integrand_bound_levi` uses radical unimodularity and the existing
`closedHalfCharacter_eq_comp_projection` theorem. The norm of the positive
complex half-character is its nonnegative real value. It therefore replaces
`norm (chiP q)` by

```
(NNReal.sqrt
  (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
    (h.projection q) : NNReal) : Real).
```

This is the positive square root of the actual Levi action's Haar scaling
character, with the positive induction convention retained.

## Remaining applications

The scalar integrand is the one used by the separately constructed compact
probability coefficient map. This module leaves that map and its measure
unchanged. It supplies no comparison with the older arbitrary-scale Bruhat
measure or coefficient map.

To obtain the source uniform family estimate one must still prove the Levi
coefficient estimate, identify ξ with the actual Levi spherical function,
transport fixed compact-model values through unitary unramified twists,
produce the parabolic–compact factorizations, and justify integration and
the precise measure comparison with II.1.6. No full VI.2.2 bound, general
reductive rational-point realization, compact-choice independence, Schwartz
membership, wave packet theorem or Plancherel inversion is asserted here.
