# `K`-valued points of analytifications of separated algebraic spaces

`SpaceAnalytificationFieldPointsStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field, `X` a separated algebraic space
over `Spec K` that is locally of finite type, and `(Y, p)` an analytification of
`X` in the sense of `IsAnalytification`. Then:
1. a `K`-valued point of `Y` is determined by its underlying point. That is, the
   projection `(localizedFieldPointProjection K).app Y` from the `K`-valued
   points of `Y` to its underlying points is injective;
2. for every finite polynomial presentation `P₀` of `K`, there is a bijection
   `e` from the `K`-points `RingPoints K X K` of `X` to the `K`-valued points
   `(localizedFieldPointFunctor K).obj Y` of `Y`. For every `K`-point `x`, the
   underlying point of `e x` is `rationalPoint p P₀ x`.

So the image of `rationalPoint p P₀` is exactly the set of underlying points of
the `K`-valued points of `Y`, and `rationalPoint p P₀` is injective. This module
states the proposition only; it supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- an algebraic space `X` over `Spec (CommRingCat.of K)` with `IsSeparated X` and
  `LocallyOfFiniteTypeOverBase X`;
- `Y : LocalizedCategory.{u, u, u}`, `p : PointFamily K X Y` and
  `IsAnalytification K X Y p`.

The conclusion is
`Function.Injective ((localizedFieldPointProjection K).app Y) ∧ ∀ P₀,
∃ e : RingPoints K X K ≃ (localizedFieldPointFunctor K).obj Y,
∀ x, ULift.down ((localizedFieldPointProjection K).app Y (e x)) =
rationalPoint p P₀ x`.

The `K`-valued points are the Library's field-valued points (module
`FieldValuedPoints`) with values in `L = K`, through its normed-algebra
structure over itself. Such a point is a point `y` of the space with, for every
chart of the saturated atlas containing `y`, a `K`-algebra map from the chart
algebra to `K`. Its absolute value is the multiplicative seminorm of `y` in that
chart, and the maps are compatible with restrictions. The functor
`localizedFieldPointFunctor K` is these points on the localized category, and
`localizedFieldPointProjection K` sends such a point to its underlying point
(wrapped in `ULift`).

`rationalPoint p P₀ x` is the image, under the map attached to the `K`-point
`x`, of the analytic point of the identity `K`-point of `K`. The statement does
not say how `e` is built. It does not state naturality of `e` in `X` as a
separate clause.

## Provenance

The first source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), says that the analytification `Xᵃⁿ` of a
separated algebraic space locally of finite type "satisfies the expected
functorial property `X(k) = Xᵃⁿ(k)` as sets", by [CT, Ex. 2.3.2].

The second source is Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`. Example
2.3.2, printed pp.11–12, constructs a map from the set `|X|₀` of closed points
of `X` to the points of `Xᵃⁿ`, shows that it is bijective "by a fiber product
argument", and notes that it preserves residue fields over `k`.

The third source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, §1.4,
printed p.30. It attaches to each point `x` of an analytic space a field
`ℋ(x)`, with a canonical bounded character `𝒜_V → ℋ(x)` for every affinoid
domain `V` containing `x`.

The formulation is derived. Conrad works with the rigid space `Xᵃⁿ` and its
`k`-points, the rigid points with residue field `k`. In the Berkovich space
these are the points `y` with `ℋ(y) = K`. A `K`-valued point in the sense of
`FieldValuedPoints` is such a point together with its characters into `K`.
Clause 1 says these characters carry no extra data, so the set of `K`-valued
points is a subset of the underlying space. The bijection in clause 2 is
compatible with `rationalPoint`. The hypotheses, separated and locally of finite
type, are those of the Library's existence statement
`SpaceAnalytificationExistenceStatement`.

## Why the statement should be true

Clause 1. The charts of an atlas are injective, since they are embeddings, so
the spectrum point of `y` in a chart is determined by `y`. Let `χ` and `χ'` be
two `K`-algebra maps from the chart algebra to `K` with `|χ(a)| = |χ'(a)|` equal
to the seminorm of `y` at every `a`. For each `a`, the element `a - χ(a)` has
seminorm `|χ(a - χ(a))| = 0`. So `χ'(a - χ(a)) = 0`, that is,
`χ'(a) = χ(a)`. Hence the evaluations agree at every chart.

Clause 2. Every analytification is isomorphic to Conrad–Temkin's `Xᵃⁿ`, and
field-valued points are functorial, so it suffices to treat `Xᵃⁿ`. The
`K`-points of `X` are the closed points of `X` with residue field `K`. By
Conrad–Temkin, Example 2.3.2, these correspond bijectively to the points of
`Xᵃⁿ` with `ℋ(y) = K`. By clause 1, these are the underlying points of the
`K`-valued points. On `K`-points, the correspondence sends `x` to the image of
the unique point of `Spec(K)ᵃⁿ` under the map attached to `x`, which is
`rationalPoint p P₀ x`. Injectivity of `rationalPoint p P₀` is also part of
`SpaceAnalytificationRationalPointsStatement`.
