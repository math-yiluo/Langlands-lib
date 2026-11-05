# Proof: smooth rational-point openness over Henselian ultrametric fields

Author: Worker 239.

`Langlands.AlgebraicGeometry.PointTopology.henselianSmoothRationalPointOpenMap` proves the
published proposition `HenselianSmoothRationalPointOpenMapStatement.{u}` of
[HenselianSmoothOpenMapStatement](HenselianSmoothOpenMapStatement.md) for every universe
`u`. Let `K : Type u` be a nontrivially normed field with `IsUltrametricDist K` and Henselian
norm valuation ring `(NormedField.valuation (K := K)).valuationSubring`. Let `X Y` be affine
over `Spec K` and `f : X ⟶ Y` with `Smooth f.left`. Then `p ↦ p ≫ f` is an open map
`RationalPoint K X → RationalPoint K Y` for `rationalPointTopology`. The proof adds no
completeness, local compactness, finite-type or characteristic hypothesis. The analytic
input is in [HenselianRootLifting](HenselianRootLifting.md).

The helper declarations below are in the namespace
`Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpen`. Their topologies are the
actual evaluation topologies on `AlgPoint`.

## Standard étale presentations

Let `A` and `B` be `K`-algebras with `Algebra A B` and a scalar tower, and let
`P : StandardEtalePresentation A B`. `StandardEtalePointCoordinates P` is the subtype of pairs
`(p, x) : AlgPoint K A K × K` with `P.f` vanishing and `P.g` not vanishing at `x` after
moving the coefficients by `p`.

- `standardEtalePoint_simple`: at such a pair, the moved derivative of `P.f` does not vanish
  at `x`. Evaluate the presentation's Bezout identity `P.cond` at `(p, x)`: the terms
  containing `P.f` and its derivative vanish, while a power of `P.g` does not. The argument is
  the same as for the private lemma of the complete-field proof `StandardEtaleOpenProof`.
- `eventually_exists_near_root`: let `z = (p₀, a₀)` be a coordinate point and `ε > 0`. Then
  every coefficient point `p` near `p₀` admits `x` with moved `P.f` vanishing at `x` and
  `dist x a₀ < ε`. Apply `HenselianRoot.eventually_exists_root` to the family
  `G p = taylor a₀ (P.f.map p)` on `T = AlgPoint K A K`. Its `k`-th coefficient is the moved
  `k`-th Hasse derivative of `P.f` evaluated at `a₀` (`taylor_coeff`, `hasseDeriv_map`). This
  is continuous in `p` by the published `continuous_point_polynomial_eval`. The degree is at
  most `P.f.natDegree`. At `p₀`, the constant coefficient is the moved value at `a₀`, which
  is `0`. The linear coefficient is the moved derivative at `a₀`, nonzero by
  `standardEtalePoint_simple`. A root `y` of `G p` with `‖y‖ < ε` gives the root `y + a₀`
  (`taylor_eval`).
- `isOpenMap_standardEtale`: restriction along `IsScalarTower.toAlgHom K A B` is open. It
  suffices to show that the projection `z ↦ z.1.1` from coordinates is open, because
  restriction is this projection composed with the published homeomorphism
  `standardEtalePointHomeomorph`. An open set of coordinates is the preimage of an open `V` in
  `AlgPoint K A K × K`. Given `z` in it, intersect `V` with the open set where moved `P.g` is
  nonzero (`isOpen_ne_fun`). This intersection contains a product neighborhood `u ×ˢ v` of
  `z`, and `v` contains a ball of radius `ε` about `a₀`. For `p ∈ u` near `p₀`,
  `eventually_exists_near_root` supplies a root `x` in that ball. So `(p, x)` lies in
  `V`, moved `P.g` does not vanish there, and `(p, x)` is a coordinate point over `p` in
  the open set.

## Smooth algebras and affine schemes

- `isOpenMap_smoothAlgebra`: for `Algebra.Smooth A B`, restriction along
  `IsScalarTower.toAlgHom K A B` is open on `K`-points. The proof is that of the published
  complete-field theorem `smoothAlgebraPointOpen` (`SmoothAlgebraOpenProof`), with its
  standard étale step replaced by `isOpenMap_standardEtale`. At a point `q`, Mathlib's
  `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` at the prime `ker q` gives
  `f ∉ ker q` such that `Localization.Away f` is standard étale over a polynomial
  algebra `MvPolynomial (Fin n) A`. Restriction from the localization factors as
  restriction along this standard étale map followed by the open projection
  `AlgPoint.isOpenMap_precomp_mvPolynomial`, so the composite from points of the
  localization to points of `A` is open. Since `q f ≠ 0`, `AlgPoint.localizationPointEquiv`
  lifts `q` to a point `ql` of the localization restricting to `q`. Given an open `U ∋ q`,
  its preimage in the localization's points is open and contains `ql`. Its image under the
  open composite is therefore an open neighborhood of the restriction of `q`, contained in
  the image of `U`.
- `isOpenMap_affineSmoothPointMap`: for affine `X`, `Y` over `Spec K` and smooth
  `f : X ⟶ Y`, postcomposition is open on `RingPoint K X K`. Smoothness of `f.left` gives
  `RingHom.Smooth` for `f.left.appTop.hom` (Mathlib's `HasRingHomProperty.iff_of_isAffine`).
  Making the coordinate pullback an algebra structure, `isOpenMap_smoothAlgebra` applies.
  `affineSchemePointEquiv_natural` and the published `affineSchemePointHomeomorph` transport
  the result. This copies the complete-field `isOpenMap_affineSmoothPointMap` of
  `CompleteFieldSmoothOpenProof` with the new algebra step.

## Main proof

After installing the statement's `rationalPointTopology` instances,
`rationalPointEquiv_natural` shows that `p ↦ p ≫ f` equals

```text
(rationalPointHomeomorph K Y).symm ∘ (q ↦ q ≫ f) ∘ rationalPointHomeomorph K X,
```

with the middle map on `RingPoint`s. It is open by `isOpenMap_affineSmoothPointMap`;
homeomorphisms are open, and composites of open maps are open.

## Provenance

Derived internal infrastructure; see the provenance section of the statement Markdown
(Kaletha–Prasad 2023, Lemma 2.5.12, with the 2024 corrections). The implemented route
follows the statement Markdown's intended route: simple-root lifting by Henselianity
after translation and scaling, standard étale neighborhoods, local smooth factorizations
through polynomial algebras, and the actual coordinate homeomorphisms.
