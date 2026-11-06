# Continuous represented Levi projection and induction admissibility

Authors: Worker 15 and Worker 1585.

Module: `Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility`.
Namespace: `Langlands.Aubert.General.RepresentedParabolic`.

This is an internal construction and adapter for the published represented-parabolic
functors. It bundles the actual Levi projection as a continuous homomorphism and
uses the published compact-quotient induction theorem to obtain admissibility.
Its provenance is the existing Library constructions listed below; it introduces
no new assertion from external literature.

## Data and topologies

Let `k : Type u` be a field with a topology, and let `G`, `P`, `M`, and `U`
be group schemes over `k`. Assume that `G` has affine structure morphism.
The ambient group `rationalPoints G` has the canonical
`RationalPointFamily.pointTopology`.

The maps `p : P → G`, `l : M → P`, and `r : U → P` have the published
hypotheses `IsParabolicSubgroup p`, `IsRationalLeviSubgroup l`,
`LeviSubgroup.IsGeometricUnipotentRadical r`, and
`IsIso (subgroupMultiplication l r)`. These are the same maps and hypotheses
used by `inductionFunctor` and `leviInductionFunctor`. Their literal point
images inherit the subgroup topologies from `rationalPoints G`.

## Projection construction and implemented continuity proof

`pointImageLeviProjection p l r hp hl hr hmul` has type

```text
pointImage p →ₜ* pointImage (l ≫ p).
```

Its underlying monoid homomorphism is exactly
`(isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection`.
The theorem `pointImageLeviProjection_toMonoidHom` records this equality by
reflexivity. Thus the construction bundles the projection already used by
normalized induction.

`continuous_projection_pointImage` proves continuity as follows.

1. The closed immersion `p` identifies the canonical rational points of `P`
   homeomorphically with `pointImage p`. This is
   `rationalPointSubgroupHomeomorph` for the range subgroup functor, followed
   by `subgroupCongrContinuous` for `pointImage_eq_range_carrier`.
   Denote this identification by `eP`.
2. The published `leviPointsEquiv p l hp hl`, denoted `eM`, identifies
   `M(k)` with `pointImage (l ≫ p)`. Its source has exactly
   `leviPointTopology l hl`. Closed immersions into the affine ambient
   scheme supply the affine instances used in these point topologies.
3. The published algebraic `leviRetraction l r hr.1.isNormal`, denoted `q`,
   comes from the inverse multiplication isomorphism. Its rational-point
   map is continuous by `continuous_rationalPointMap`.
4. For `x ∈ P(k)`, `exists_pointMultiplication` writes `x = l(a) r(n)`.
   The algebraic identities `comp_leviRetraction` and
   `leviComponent_product` give `q(x) = a`. Mapping the factorization into
   `G(k)` and applying `IsSemidirectDecomposition.projection_mul` gives
   `projection (eP x) = eM (q(x))`.
5. Consequently the actual projection equals `eM ∘ q(k) ∘ eP.symm`.
   All three maps are continuous.

The construction needs no local-field, Hausdorff, local-compactness,
nonarchimedean-group, or quotient-compactness hypothesis.

## Admissibility adapters

The remaining results additionally assume that `k` is Hausdorff and that
the canonical ambient rational-point group is locally compact and
nonarchimedean. They retain independent field and representation-carrier
universes `u` and `v`.

`inductionFunctor_obj_isAdmissible` assumes
`CompactSpace (Induction.LeftQuotient (pointImage p))`. For an admissible
`σ : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p))`, it proves admissibility of
`(inductionFunctor p l r hp hr hl hmul).obj σ`. The proof applies the
published `normalizedInductionFunctor_obj_isAdmissible` from
`Aubert.General.RationalInductionDualityReduction`. The closed radical
input is `isClosed_pointImage_comp`; the continuous-projection input is
the theorem proved above.

`leviInductionFunctor_obj_isAdmissible` gives the same result for
`σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` with
`leviPointTopology l hl`. The published transported induction first
pulls back along `leviPointsEquiv.symm`. Admissibility of that pullback
is `isAdmissible_comp_continuousMulEquiv`, and the preceding theorem
then applies. The induced carrier universe remains `max u v`, as in
the published induction functor.

`leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement`
additionally assumes the local-field instances and connected reductivity
of `G`. It takes
`hcompact : ArbitraryParabolicQuotientCompactStatement.{u}` explicitly,
installs the compactness instance `hcompact k G hG P p hp`, and applies
the preceding theorem. This is a conditional corollary.

No irreducibility, finite-length, standardness, presentation-existence, or
Jacquet-admissibility assumption occurs in these adapters. Compactness
of the actual parabolic quotient remains an explicit input to the
admissibility theorems. This module does not prove that compactness
statement or `LeviInductionNormalizedTemperedStatement`, and proves
no exponent-cone condition.
